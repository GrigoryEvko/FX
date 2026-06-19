import FX1Poly.Typed.Metatheory.Denote.Universe.DenoteKeyedFlatFormerFundamental
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationConstructors

/-! # FX1Poly/Typed/DenoteKeyedFlatFormerFromCarriers
    — flat-former formation FT fully discharged from the carriers' SN (FTGEN-5, the leaf-closed family)

`DenoteKeyedFlatFormerFundamental.flatFormerFundamentalAtDenote` proved a flat former is a
`FundamentalConclusionAtDenote` member of its universe MODULO the former's own strong normalization (the
honest telescope residual).  This file DISCHARGES that residual for the two-carrier flat formers
(equivCode / productCode / sumCode / eitherCode / arrowCode): each former's SN follows structurally from its
two carriers' SN (the shipped congruence-only `*_isStronglyNormalizing_of_*` lemmas — a flat code has no root
redex, so its only steps are congruence through the carriers), and the carriers' SN under every closing
substitution is exactly what their own formation fundamentals supply.

So the flat-former formation FT is now a pure FUNCTION of its carriers' SN-under-substitution — no former-SN
premise, no route-A composite-domain piArm (#752).  This is the leaf-closed shape the FT telescope feeds: a
flat type former applied to reducible carriers is itself a reducible member of its classifying universe.

`equivCodeFundamentalFromCarriers` is the headline — the equivalence type former, the univalence carrier — now
with its formation FT closed down to its two carrier types' strong normalization.

## Zero-axiom verification

Each is `flatFormerFundamentalAtDenote` (flat pin `rfl` — `Generator.isFlatDataCode` computes `true` on the
concrete flat generator) fed the per-former congruence-SN lemma applied to the carriers' SN; the substituted
former's SN matches the per-former lemma's conclusion by the concrete-generator `subst` reduction
(`RawTerm.subst_mkGen_of_ne_var`, `rfl` on a concrete head).  No `induction`, no `funext`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **★ FTGEN-5 headline — equivCode formation FT closed to its carriers' SN.**  The equivalence type former
`equivCode(source, target)` is a `FundamentalConclusionAtDenote` member of its classifying universe given only
that both carrier types are strongly normalizing under every closing substitution + reducible environment — the
SN of the former itself is discharged structurally via `equivCode_isStronglyNormalizing_of_source_target`.  The
univalence carrier's formation FT, route-A-free, leaf-closed. -/
theorem equivCodeFundamentalFromCarriers {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope)
    (sourceCarrier targetCarrier : RawTerm scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (sourceCarrierStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution sourceCarrier))
    (targetCarrierStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution targetCarrier)) :
    FundamentalConclusionAtDenote env level context
      (.mkGen .gen_equivCode () (.childCons sourceCarrier (.childCons targetCarrier .childNil)))
      (universeCodeCell levelExpr flag) :=
  flatFormerFundamentalAtDenote env level context
    (.mkGen .gen_equivCode () (.childCons sourceCarrier (.childCons targetCarrier .childNil)))
    rfl levelExpr flag levelAbove
    (fun substitution envReducible =>
      equivCode_isStronglyNormalizing_of_source_target
        (sourceCarrierStronglyNormalizing substitution envReducible)
        (targetCarrierStronglyNormalizing substitution envReducible))

/-- **Product type code formation FT closed to its components' SN.**  `productCode(left, right)` is a
`FundamentalConclusionAtDenote` member of its universe given both component types are SN under every closing
substitution; the former's SN via `productCode_isStronglyNormalizing_of_left_right`. -/
theorem productCodeFundamentalFromCarriers {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope)
    (leftType rightType : RawTerm scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (leftStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution leftType))
    (rightStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution rightType)) :
    FundamentalConclusionAtDenote env level context
      (.mkGen .gen_productCode () (.childCons leftType (.childCons rightType .childNil)))
      (universeCodeCell levelExpr flag) :=
  flatFormerFundamentalAtDenote env level context
    (.mkGen .gen_productCode () (.childCons leftType (.childCons rightType .childNil)))
    rfl levelExpr flag levelAbove
    (fun substitution envReducible =>
      productCode_isStronglyNormalizing_of_left_right
        (leftStronglyNormalizing substitution envReducible)
        (rightStronglyNormalizing substitution envReducible))

/-- **Sum type code formation FT closed to its summands' SN.**  `sumCode(left, right)`, SN via
`sumCode_isStronglyNormalizing_of_left_right`. -/
theorem sumCodeFundamentalFromCarriers {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope)
    (leftType rightType : RawTerm scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (leftStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution leftType))
    (rightStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution rightType)) :
    FundamentalConclusionAtDenote env level context
      (.mkGen .gen_sumCode () (.childCons leftType (.childCons rightType .childNil)))
      (universeCodeCell levelExpr flag) :=
  flatFormerFundamentalAtDenote env level context
    (.mkGen .gen_sumCode () (.childCons leftType (.childCons rightType .childNil)))
    rfl levelExpr flag levelAbove
    (fun substitution envReducible =>
      sumCode_isStronglyNormalizing_of_left_right
        (leftStronglyNormalizing substitution envReducible)
        (rightStronglyNormalizing substitution envReducible))

/-- **Either type code formation FT closed to its sides' SN.**  `eitherCode(left, right)`, SN via
`eitherCode_isStronglyNormalizing_of_left_right`. -/
theorem eitherCodeFundamentalFromCarriers {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope)
    (leftType rightType : RawTerm scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (leftStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution leftType))
    (rightStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution rightType)) :
    FundamentalConclusionAtDenote env level context
      (.mkGen .gen_eitherCode () (.childCons leftType (.childCons rightType .childNil)))
      (universeCodeCell levelExpr flag) :=
  flatFormerFundamentalAtDenote env level context
    (.mkGen .gen_eitherCode () (.childCons leftType (.childCons rightType .childNil)))
    rfl levelExpr flag levelAbove
    (fun substitution envReducible =>
      eitherCode_isStronglyNormalizing_of_left_right
        (leftStronglyNormalizing substitution envReducible)
        (rightStronglyNormalizing substitution envReducible))

/-- **Arrow type code formation FT closed to its endpoints' SN.**  `arrowCode(domain, codomain)` (the
non-dependent function code), SN via `arrowCode_isStronglyNormalizing_of_domain_codomain`. -/
theorem arrowCodeFundamentalFromCarriers {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope)
    (domainType codomainType : RawTerm scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (domainStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution domainType))
    (codomainStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution codomainType)) :
    FundamentalConclusionAtDenote env level context
      (.mkGen .gen_arrowCode () (.childCons domainType (.childCons codomainType .childNil)))
      (universeCodeCell levelExpr flag) :=
  flatFormerFundamentalAtDenote env level context
    (.mkGen .gen_arrowCode () (.childCons domainType (.childCons codomainType .childNil)))
    rfl levelExpr flag levelAbove
    (fun substitution envReducible =>
      arrowCode_isStronglyNormalizing_of_domain_codomain
        (domainStronglyNormalizing substitution envReducible)
        (codomainStronglyNormalizing substitution envReducible))

end FX1Poly.Typed
