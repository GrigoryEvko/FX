import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Typed.HasTypeHonesty

/-! # FX1Poly/Typed/HasTypeDescInversion — INVERSION (P8 descent) for the description engine.

polycell.md §11.8.5 P8 ("Inversion = descent"): `HasType Γ (mkGen g p ch) T ⇒
children typed at the TypingRule's expected types ∧ Conv T (rule.outputType …)`,
"one lemma per shape; feeds the typechecker and canonicity" — the sheaf/glue
direction.  This ships the PREMISE half of P8 for the FORMATION shape on the
description engine `HasTypeDesc`: from a formation cell's typing, recover the
`DescTelescope` premise witnessing its children form the expected telescope of types.

Why the premise half is the right cut: **it is `Conv`-FREE.**  Full P8's
classifier-`Conv` conjunct needs `Conv.trans` on the `conv` arm (the abandoned raw-CR
route; typed `Conv.trans_of_typedMiddle` only with a `WfContext`).  But the CHILDREN
are determined by the SUBJECT (`mkGen g p ch`), which `conv` leaves unchanged — so the
`conv` arm forwards the descent IH VERBATIM, needing no `Conv` and no `WfContext`.
This isolates the genuinely-useful descent content (the children's telescope — what
the typechecker + canonicity consume) from the `Conv`-blocked part.

Shipped this fire for the Π-formation shape (`piTyCodeCell`); the Σ shape over
`gen_sigmaTyCode` is the identical mirror (a future atomic step).  A FULLY generic
version (one descent lemma over every whitelisted generator, refuting non-formers via
`typingRuleDescOf … = none`) is attractive but blocked by a dependent-`subst` wall:
unifying a free generator variable with the arm's generator fails Lean's
scope/occurs check both directions.  The concrete-former shape sidesteps it
(`subst armGenerator := gen_piTyCode` against a CONSTANT is clean) — which is exactly
why the bespoke layer also ships `inversionPiCode`/`inversionSigmaCode` as a pair.

## Recipe (equation-motive, adapted to the MUTUAL engine)

`induction` REJECTS `HasTypeDesc` ("mutually inductive"), so the recursion is a
term-mode recursive `match` (the propext-free structural form of the shipped
`HasTypeDesc.toHasType`) in a helper generalizing the subject + threading `subject =
mkGen g p ch`.  It recurses ONLY into the `conv` premise — a LONE recursion on
`HasTypeDesc` (no mutual block), exactly as `DescTelescope.toTermTelescope` recurses
on one mutual member alone.

* `var` / `universeFormation` — impossible: `congrArg RawTerm.headGenerator` on the
  subject equation gives `gen_var = gen_piTyCode` / `gen_universeCode = gen_piTyCode`,
  killed by `Generator.noConfusion` (both generators concrete — no `typingRuleDescOf`
  reduction needed).
* `conv` — forwards the recursive call on its premise (same subject), unchanged.
* `genFormation` — the principal arm: `headGenerator` gives `armGenerator =
  gen_piTyCode`; `subst` (against the CONSTANT `gen_piTyCode`) makes both sides of the
  subject equation literal `mkGen gen_piTyCode …`; `injection` + `subst_vars` align the
  arm's children with the target; the arm's `DescTelescope` premise IS the result.

## Zero-axiom

Term-mode recursive `match` + `congrArg RawTerm.headGenerator` + `Generator.noConfusion`
+ `injection` + `subst_vars`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The equation-motive recursive workhorse for formation-shape descent: subject
generalized to a free variable, threading `subject = mkGen generator payload children`
and the `typingRuleDescOf generator = some rule` whitelist witness.  Recursion via
term-mode `match` (the `conv` arm recurses on its structurally-smaller premise; every
other arm is a leaf), so this is a LONE structural recursion on the mutual
`HasTypeDesc`. -/
theorem HasTypeDesc.inversionPiCodeGeneral {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject reachedClassifier : RawTerm generalScope}
    (derivation : HasTypeDesc profile generalContext subject reachedClassifier) :
    ∀ {payload : Generator.gen_piTyCode.payload generalScope}
      {children : RawTermChildren Generator.gen_piTyCode.binderShifts generalScope},
      subject = RawTerm.mkGen Generator.gen_piTyCode payload children →
        ∃ (levels : List LevelExpr) (flag : UniverseFlag),
          DescTelescope profile (currentDepth := 0) generalContext levels flag
            children :=
  fun {payloadImplicit} {childrenImplicit} =>
    match derivation with
    | .var _armContext _armIndex => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_var = Generator.gen_piTyCode)
    | .conv _levelExpr _flag typedPremise _converts _reclassifierTyped =>
        fun subjectEq => HasTypeDesc.inversionPiCodeGeneral typedPremise subjectEq
    | .universeFormation _armContext _armLevel _armFlag => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_universeCode = Generator.gen_piTyCode)
    | .genFormation _armContext armGenerator _armPayload armChildren armLevels armFlag
        _armRule _armIsFormation armPremises => fun subjectEq => by
        have generatorAgree : armGenerator = Generator.gen_piTyCode :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorAgree
        injection subjectEq
        subst_vars
        exact ⟨armLevels, armFlag, armPremises⟩

/-- **Inversion (P8 descent, premise half) for the Π-type FORMATION shape** on the
description engine.  Any `HasTypeDesc`-typing of `piTyCodeCell domainCode
codomainCode` arises — through `conv` — from a `genFormation` whose `DescTelescope`
premise types the two children as the expected telescope of types.  `Conv`-free (the
children are fixed by the subject, so `conv` forwards the descent IH verbatim — no
`Conv.trans`, no `WfContext`); feeds the typechecker and canonicity.  The
description-engine analogue of the bespoke `inversionPiCode`.  (The Σ shape is the
mirror over `gen_sigmaTyCode` — a future atomic step; the recipe is identical.) -/
theorem HasTypeDesc.inversionPiCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {classifier : RawTerm scope}
    (typed :
      HasTypeDesc profile context (piTyCodeCell domainCode codomainCode) classifier) :
    ∃ (levels : List LevelExpr) (flag : UniverseFlag),
      DescTelescope profile (currentDepth := 0) context levels flag
        (RawTermChildren.binderShape domainCode codomainCode) :=
  HasTypeDesc.inversionPiCodeGeneral typed rfl

end FX1Poly.Typed
