import LeanFX2.Foundation.RawSubst.SubstDefs

/-! # Algo/RawWHNF — fuel-bounded weak head normal form on raw terms

`RawTerm.whnf : Nat → RawTerm scope → RawTerm scope` reduces a raw
term to weak head normal form by repeatedly firing β/ι at the head.
The fuel parameter ensures termination regardless of strong-
normalization status (Tot terms terminate naturally; Div terms get
truncated at the fuel ceiling).

## Why raw-side first

Typed `Term.whnf` would need to thread typed Term constructors and
HEq-cast through every β/ι contractum.  Raw-side `RawTerm.whnf`
operates on plain data — no dependent indices, no type-level
threading.  Once we have the raw operation, we lift via the typed-
to-raw bridge.

## Reduction strategy

Call-by-name: head reduction first.  No reduction under binders
beyond the head.

## Termination

The function terminates structurally on the `Nat` fuel parameter.
No SN proof required; if fuel is exhausted, return the term as-is
(which may not be in WHNF — caller's responsibility to use
sufficient fuel).

## Architecture: zero-axiom recipe

Three discipline rules keep this function propext-free:

1. **Outer Nat match, inner RawTerm match** — combining a Nat
   ctor pattern (`0` vs `_+1`) with a dependent RawTerm pattern
   in a single multi-discriminator match leaks propext.  The
   workaround is to nest: outer `match fuel with`, inner
   `match term with`.

2. **Full enumeration in every match arm** — every `match` over
   `RawTerm` or over `RawTerm.HeadCtor` lists every constructor
   explicitly (no `| _ => ...` wildcards).  Wildcards on
   dependent inductives leak propext per
   `feedback_lean_zero_axiom_match.md`.

3. **Flat-enum dispatch via `headCtor`** — when we only need to
   know "did the recursively-whnf'd subterm reach a canonical
   form?", we project to `RawTerm.HeadCtor` (a flat enum) and
   match there.  Component extraction is delegated to dedicated
   `?`-projection helpers (`lamBody?`, `pairComponents?`, ...)
   each of which uses full 28-arm enumeration.
-/


namespace LeanFX2

/-- Flat enum tagging the head constructor of a `RawTerm`.  Used
by `RawTerm.whnf` to dispatch on the head shape of a recursively-
whnf'd subterm without nested pattern-matches that would leak
propext via wildcards. -/
inductive RawTerm.HeadCtor : Type
  | var | unit | lam | app | pair | fst | snd
  | boolTrue | boolFalse | boolElim
  | natZero | natSucc | natElim | natRec
  | listNil | listCons | listElim
  | optionNone | optionSome | optionMatch
  | eitherInl | eitherInr | eitherMatch
  | refl | idJ
  | modIntro | modElim | subsume
  -- D1.6 cubical / HOTT / refine / record / codata / session / effect / strict
  | interval0 | interval1 | intervalOpp | intervalMeet | intervalJoin
  | pathLam | pathApp | glueIntro | glueElim | transp | hcomp | transpFill
  | oeqRefl | oeqJ | oeqFunext | idStrictRefl | idStrictRec
  | equivIntro | equivApp | refineIntro | refineElim
  | recordIntro | recordProj | codataUnfold | codataDest
  | sessionSend | sessionRecv | effectPerform
  | universeCode
  -- CUMUL-2.1 per-shape type codes
  | arrowCode | piTyCode | sigmaTyCode | productCode | sumCode
  | listCode | optionCode | eitherCode | idCode | equivCode
  -- CUMUL-2.6: cumulUpMarker
  | cumulUpMarker
  -- D3.6-P1: univalence-to-equiv vocabulary
  | uaToEquiv
  -- D3.6-P2: equivApply vocabulary
  | equivApply
  -- D3.6-S3: pathCompose vocabulary
  | pathCompose
  -- D3.6-S4: idToEquiv vocabulary
  | idToEquiv
  -- D3.6-S5: oeqTrans vocabulary
  | oeqTrans
  -- D3.6-S5: equivCompose vocabulary
  | equivCompose

/-- Project a raw term to its head-ctor tag.  Full enumeration of
all 28 RawTerm ctors keeps this propext-free. -/
def RawTerm.headCtor {scope : Nat} (term : RawTerm scope) : RawTerm.HeadCtor :=
  match term with
  | .var _ => .var | .unit => .unit | .lam _ => .lam
  | .app _ _ => .app | .pair _ _ => .pair
  | .fst _ => .fst | .snd _ => .snd
  | .boolTrue => .boolTrue | .boolFalse => .boolFalse
  | .boolElim _ _ _ => .boolElim
  | .natZero => .natZero | .natSucc _ => .natSucc
  | .natElim _ _ _ => .natElim | .natRec _ _ _ => .natRec
  | .listNil => .listNil | .listCons _ _ => .listCons
  | .listElim _ _ _ => .listElim
  | .optionNone => .optionNone | .optionSome _ => .optionSome
  | .optionMatch _ _ _ => .optionMatch
  | .eitherInl _ => .eitherInl | .eitherInr _ => .eitherInr
  | .eitherMatch _ _ _ => .eitherMatch
  | .refl _ => .refl | .idJ _ _ => .idJ
  | .modIntro _ => .modIntro | .modElim _ => .modElim
  | .subsume _ => .subsume
  -- D1.6
  | .interval0 => .interval0 | .interval1 => .interval1
  | .intervalOpp _ => .intervalOpp
  | .intervalMeet _ _ => .intervalMeet
  | .intervalJoin _ _ => .intervalJoin
  | .pathLam _ => .pathLam | .pathApp _ _ => .pathApp
  | .glueIntro _ _ => .glueIntro | .glueElim _ => .glueElim
  | .transp _ _ => .transp | .hcomp _ _ => .hcomp
  | .transpFill _ _ _ => .transpFill
  | .oeqRefl _ => .oeqRefl | .oeqJ _ _ => .oeqJ
  | .oeqFunext _ => .oeqFunext
  | .idStrictRefl _ => .idStrictRefl | .idStrictRec _ _ => .idStrictRec
  | .equivIntro _ _ => .equivIntro | .equivApp _ _ => .equivApp
  | .refineIntro _ _ => .refineIntro | .refineElim _ => .refineElim
  | .recordIntro _ => .recordIntro | .recordProj _ => .recordProj
  | .codataUnfold _ _ => .codataUnfold | .codataDest _ => .codataDest
  | .sessionSend _ _ => .sessionSend | .sessionRecv _ => .sessionRecv
  | .effectPerform _ _ => .effectPerform
  | .universeCode _ => .universeCode
  -- CUMUL-2.1 per-shape type codes
  | .arrowCode _ _ => .arrowCode
  | .piTyCode _ _ => .piTyCode
  | .sigmaTyCode _ _ => .sigmaTyCode
  | .productCode _ _ => .productCode
  | .sumCode _ _ => .sumCode
  | .listCode _ => .listCode
  | .optionCode _ => .optionCode
  | .eitherCode _ _ => .eitherCode
  | .idCode _ _ _ => .idCode
  | .equivCode _ _ => .equivCode
  | .cumulUpMarker _ => .cumulUpMarker
  | .uaToEquiv _ => .uaToEquiv
  | .equivApply _ _ => .equivApply
  | .pathCompose _ _ => .pathCompose
  | .idToEquiv _ => .idToEquiv
  | .oeqTrans _ _ => .oeqTrans
  | .equivCompose _ _ => .equivCompose

end LeanFX2
