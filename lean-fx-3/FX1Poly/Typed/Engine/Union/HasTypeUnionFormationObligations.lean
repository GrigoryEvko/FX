import FX1Poly.Typed.Engine.Union.HasTypeUnion

/-! # FX1Poly/Typed/HasTypeUnionFormationObligations — the formationRule arm's union-obligation toolkit

After the TYTAB-2 formationRule promotion, the `formationRule` arm premises a UNION obligation list
(`rule.obligations …`), exactly like the `intro` / `elim` arms.  Two pieces are needed downstream:

  * `HasTypeUnion.formationRuleOfObligations` — the reconstruction primitive: build a `formationRule`
    typing from the union premise DIRECTLY (no grown telescope, no bridge).  This is what the
    destructure-and-rebuild consumers (weakening / substitution / subject reduction) use, and the
    construction primitive a dependent-type-producing beta reduct needs when its children are
    genuinely union-typed (the W4 frontier).

  * The OBLIGATION-LIST PUSH lemmas — the generic statement that renaming / substitution commutes with
    the variable-length obligation fold (`flatFormationObligations` / `termIndexedEndpointObligations`),
    at the membership level.  These take the per-source-obligation transported typing (exactly the arm's
    induction hypothesis `ihPremises`) and produce the target arm's `premisesHold` over the
    renamed / substituted children — the genuine push-through, NOT a grown reflection (which is false:
    a native eliminator-type like `fst pair` is union-typed at a universe but has no host typing).

  Because the obligation list is a fold over an ARBITRARY children spine (a formation generator is only
  `cases`'d into its three families, never `rcases`'d to a concrete row), the push is a generic
  structural recursion over the spine — once, covering every present and future formation former
  (W-types, quotients) for free.

## Zero-axiom

Structural recursion over the `RawTermChildren` spine + `cases` on `List.Mem` constructors (NOT the
`mem_map` / `mem_append` iff lemmas, which leak `propext`) + the closed-cell `subst`/`rename`
commutations (`subst_universeCodeCell` / `rename_universeCodeCell`).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- ★ **The union-obligation `formationRule` builder.**  Builds a `formationRule` typing from the UNION
premise directly (the raw arm constructor at the canonical bundle), the twin of `HasTypeUnion.elim` /
`HasTypeUnion.intro`.  Unlike `HasTypeUnion.formationRule` (which takes a GROWN telescope and bridges via
`formationPremiseToObligations`), this takes the obligation list typed already — the reconstruction
primitive for the metatheory consumers and the construction primitive for union-childed type formers. -/
@[reducible] def HasTypeUnion.formationRuleOfObligations {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator)
    (payload : generator.payload scope) (children : RawTermChildren generator.binderShifts scope)
    (rule : FormationRule) (levels : List LevelExpr) (carrier : RawTerm scope)
    (level : LevelExpr) (flag : UniverseFlag)
    (isFormationRule : formationRuleOf generator = some rule)
    (premisesHold : ∀ obligation ∈ rule.obligations profile context children levels carrier level flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    HasTypeUnion profile context (.mkGen generator payload children)
      (rule.outputType scope levels level flag) :=
  HasTypeUnionOver.formationRule (bundle := fxTypingBundle) context generator payload children rule
    levels carrier level flag isFormationRule premisesHold

/-- **The flat-family obligation SUBSTITUTION push.**  Condition-free and scope-clean: the hypothesis
delivers, per source flat child (named EXPLICITLY at `sourceScope` so the substitution typechecks with no
transport), the union typing of its substituted form at the closed universe code; the conclusion is every
target obligation over the substituted children, union-typed.  The consumer threads its `ihPremises` +
the substitution side condition when it builds the hypothesis — keeping `SubstHostTyped` (a downstream
abbrev) out of this file.  Generic over the spine: induct on the shape `binderShifts` (a plain `List Nat`)
+ `cases` the mutual `RawTermChildren` (the `induction` tactic rejects the mutual inductive, `cases` does
not).  The genuine union push-through — no telescope, no host reflection. -/
theorem flatFormationObligations_pushSubst {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (substitution : RawTermSubst sourceScope targetScope) (flag : UniverseFlag) :
    ∀ {binderShifts : List Nat} (children : RawTermChildren binderShifts sourceScope)
      (levels : List LevelExpr),
      (∀ (subject classifier : RawTerm sourceScope),
        ({ scope := sourceScope, context := sourceContext, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ flatFormationObligations profile sourceContext flag children levels →
        HasTypeUnion profile targetContext (RawTerm.subst substitution subject)
          (RawTerm.subst substitution classifier)) →
      ∀ targetObligation ∈ flatFormationObligations profile targetContext flag
          (RawTermChildren.subst substitution children) levels,
        HasTypeUnion profile targetObligation.context targetObligation.subject
          targetObligation.classifier := by
  intro binderShifts
  induction binderShifts with
  | nil =>
      intro children levels _sourceTypings targetObligation targetMember
      cases children
      cases targetMember
  | cons headShift restShifts ih =>
      intro children levels sourceTypings targetObligation targetMember
      cases children with
      | childCons childHead childTail =>
          cases headShift with
          | zero =>
              cases levels with
              | nil =>
                  -- LEVELS EXHAUSTED: the obligation list now FORCES the remaining children at `lzero`
                  -- (closing the degenerate-`levels` escape).  Same head / tail dispatch as the `cons` case,
                  -- at the constant `lzero` level.
                  cases targetMember with
                  | head =>
                      have headTyped := sourceTypings childHead (universeCodeCell LevelExpr.lzero flag)
                        (List.Mem.head _)
                      rwa [subst_universeCodeCell] at headTyped
                  | tail _ tailMember =>
                      exact ih childTail []
                        (fun subject classifier member =>
                          sourceTypings subject classifier (List.Mem.tail _ member))
                        targetObligation tailMember
              | cons headLevel restLevels =>
                  cases targetMember with
                  | head =>
                      have headTyped := sourceTypings childHead (universeCodeCell headLevel flag)
                        (List.Mem.head _)
                      rwa [subst_universeCodeCell] at headTyped
                  | tail _ tailMember =>
                      exact ih childTail restLevels
                        (fun subject classifier member =>
                          sourceTypings subject classifier (List.Mem.tail _ member))
                        targetObligation tailMember
          | succ _ => cases targetMember

/-- **The term-indexed endpoint obligation SUBSTITUTION push.**  Every endpoint is typed at the FIXED
`carrier` classifier; under substitution the target endpoints are typed at `subst carrier`, which is
exactly what the source-endpoint typings supply — no closed-cell rewrite needed.  Same spine recursion as
the flat push. -/
theorem termIndexedEndpointObligations_pushSubst {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (substitution : RawTermSubst sourceScope targetScope) (carrier : RawTerm sourceScope) :
    ∀ {shifts : List Nat} (children : RawTermChildren shifts sourceScope),
      (∀ (subject classifier : RawTerm sourceScope),
        ({ scope := sourceScope, context := sourceContext, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ termIndexedEndpointObligations profile sourceContext carrier children →
        HasTypeUnion profile targetContext (RawTerm.subst substitution subject)
          (RawTerm.subst substitution classifier)) →
      ∀ targetObligation ∈ termIndexedEndpointObligations profile targetContext
          (RawTerm.subst substitution carrier) (RawTermChildren.subst substitution children),
        HasTypeUnion profile targetObligation.context targetObligation.subject
          targetObligation.classifier := by
  intro shifts
  induction shifts with
  | nil =>
      intro children _sourceTypings targetObligation targetMember
      cases children
      cases targetMember
  | cons headShift restShifts ih =>
      intro children sourceTypings targetObligation targetMember
      cases children with
      | childCons childHead childTail =>
          cases headShift with
          | zero =>
              cases targetMember with
              | head =>
                  exact sourceTypings childHead carrier (List.Mem.head _)
              | tail _ tailMember =>
                  exact ih childTail
                    (fun subject classifier member =>
                      sourceTypings subject classifier (List.Mem.tail _ member))
                    targetObligation tailMember
          | succ _ => cases targetMember

/-- **The cumulative-family obligation SUBSTITUTION push.**  Dispatches on the children spine (the
binder-shape Π/Σ spine vs the element-shape List/Option spine).  Condition-AGNOSTIC: it takes two plain
typing functions (no substituent-condition baked in, so it serves the host-image and union-image
substitution consumers alike).  `baseTypings` discharges the base (ambient-scope) obligations — domain /
element — exactly as the flat case (the closed-cell `subst_universeCodeCell` rewrite).  `crossingTypings`
discharges the Π/Σ BINDER-CROSSING codomain obligation, which lives at `sourceScope + 1` in the
domain-extended context: its typing is supplied under the LIFTED substitution (`iterateLiftRaw
substitution 1`) and the substituted domain-extended target context — the consumer builds it from its own
induction hypothesis at the lifted condition (the natElim step-branch discipline, here at one binder). -/
theorem cumulativeFormationObligations_pushSubst {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (substitution : RawTermSubst sourceScope targetScope) (flag : UniverseFlag) :
    ∀ {binderShifts : List Nat} (children : RawTermChildren binderShifts sourceScope)
      (levels : List LevelExpr),
      (∀ (subject classifier : RawTerm sourceScope),
        ({ scope := sourceScope, context := sourceContext, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ cumulativeFormationObligations profile sourceContext flag children levels →
        HasTypeUnion profile targetContext (RawTerm.subst substitution subject)
          (RawTerm.subst substitution classifier)) →
      (∀ (domain : RawTerm sourceScope) (subject classifier : RawTerm (sourceScope + 1)),
        ({ scope := sourceScope + 1, context := sourceContext.cons domain, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ cumulativeFormationObligations profile sourceContext flag children levels →
        HasTypeUnion profile (targetContext.cons (RawTerm.subst substitution domain))
          (RawTerm.subst (iterateLiftRaw substitution 1) subject)
          (RawTerm.subst (iterateLiftRaw substitution 1) classifier)) →
      ∀ targetObligation ∈ cumulativeFormationObligations profile targetContext flag
          (RawTermChildren.subst substitution children) levels,
        HasTypeUnion profile targetObligation.context targetObligation.subject
          targetObligation.classifier := by
  intro binderShifts children levels baseTypings crossingTypings targetObligation targetMember
  -- Mirror `cumulativeFormationObligations`'s spine dispatch so the substituted obligation list reduces.
  match binderShifts, children, levels with
  | _, .childNil, _ => cases targetMember
  -- Element spine, levels exhausted: the FORCED `headChild : Type@0` obligation (cumulative free-`levels` fix).
  | _, .childCons (shift := 0) headChild .childNil, [] =>
      cases targetMember with
      | head =>
          have elementTyped := baseTypings headChild (universeCodeCell LevelExpr.lzero flag) (List.Mem.head _)
          rwa [subst_universeCodeCell] at elementTyped
      | tail _ tailMember => cases tailMember
  | _, .childCons (shift := 0) headChild .childNil, elementLevel :: _ =>
      cases targetMember with
      | head =>
          have elementTyped := baseTypings headChild (universeCodeCell elementLevel flag) (List.Mem.head _)
          rwa [subst_universeCodeCell] at elementTyped
      | tail _ tailMember => cases tailMember
  | _, .childCons (shift := 0) domain (.childCons (shift := 1) codomain .childNil),
      domainLevel :: codomainLevel :: _ =>
      cases targetMember with
      | head =>
          have domainTyped := baseTypings domain (universeCodeCell domainLevel flag) (List.Mem.head _)
          rwa [subst_universeCodeCell] at domainTyped
      | tail _ tailMember =>
          cases tailMember with
          | head =>
              -- The binder-crossing codomain: supplied at the lifted substitution + extended context.
              have codomainTyped := crossingTypings domain codomain
                (universeCodeCell codomainLevel flag) (List.Mem.tail _ (List.Mem.head _))
              rwa [subst_universeCodeCell] at codomainTyped
          | tail _ deeperMember => cases deeperMember
  -- Π / Σ spine, levels exhausted / too short: the FORCED domain + codomain at `Type@0` (free-`levels` fix).
  | _, .childCons (shift := 0) domain (.childCons (shift := 1) codomain .childNil), [] =>
      cases targetMember with
      | head =>
          have domainTyped := baseTypings domain (universeCodeCell LevelExpr.lzero flag) (List.Mem.head _)
          rwa [subst_universeCodeCell] at domainTyped
      | tail _ tailMember =>
          cases tailMember with
          | head =>
              have codomainTyped := crossingTypings domain codomain
                (universeCodeCell LevelExpr.lzero flag) (List.Mem.tail _ (List.Mem.head _))
              rwa [subst_universeCodeCell] at codomainTyped
          | tail _ deeperMember => cases deeperMember
  | _, .childCons (shift := 0) domain (.childCons (shift := 1) codomain .childNil), [_] =>
      cases targetMember with
      | head =>
          have domainTyped := baseTypings domain (universeCodeCell LevelExpr.lzero flag) (List.Mem.head _)
          rwa [subst_universeCodeCell] at domainTyped
      | tail _ tailMember =>
          cases tailMember with
          | head =>
              have codomainTyped := crossingTypings domain codomain
                (universeCodeCell LevelExpr.lzero flag) (List.Mem.tail _ (List.Mem.head _))
              rwa [subst_universeCodeCell] at codomainTyped
          | tail _ deeperMember => cases deeperMember
  | _, .childCons (shift := 0) _ (.childCons (shift := 1) _ (.childCons _ _)), _ => cases targetMember
  | _, .childCons (shift := 0) _ (.childCons (shift := 0) _ _), _ => cases targetMember
  | _, .childCons (shift := 0) _ (.childCons (shift := _ + 2) _ _), _ => cases targetMember
  | _, .childCons (shift := _ + 1) _ _, _ => cases targetMember

/-- ★ **The unified formation-obligation SUBSTITUTION push** — the genuine union push-through, dispatched
by family.  Condition-AGNOSTIC: `baseTypings` supplies each base (ambient-scope) source obligation's typing
under the substitution (the consumer threads its own `ihPremises` + substituent condition), and
`crossingTypings` the cumulative Π/Σ codomain at `sourceScope + 1` under the LIFTED substitution (the
consumer threads `ihPremises` + the lifted condition).  Base types demand nothing; flat formers route
through `flatFormationObligations_pushSubst`; term-indexed formers discharge the carrier at the universe
code (`subst_universeCodeCell`) and the endpoints through `termIndexedEndpointObligations_pushSubst`;
cumulative formers route through `cumulativeFormationObligations_pushSubst` (binder-crossing codomain at the
lifted substitution).  No telescope, no host reflection — covers every present and future formation former
by the generic spine recursion. -/
theorem FormationRule.obligations_pushSubst {profile : PolyProfile}
    {sourceScope targetScope : Nat} (rule : FormationRule)
    {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (substitution : RawTermSubst sourceScope targetScope)
    {binderShifts : List Nat} (children : RawTermChildren binderShifts sourceScope)
    (levels : List LevelExpr) (carrier : RawTerm sourceScope) (level : LevelExpr) (flag : UniverseFlag)
    (baseTypings : ∀ (subject classifier : RawTerm sourceScope),
      ({ scope := sourceScope, context := sourceContext, subject := subject,
         classifier := classifier } : ElimObligation profile)
        ∈ rule.obligations profile sourceContext children levels carrier level flag →
      HasTypeUnion profile targetContext (RawTerm.subst substitution subject)
        (RawTerm.subst substitution classifier))
    (crossingTypings : ∀ (domain : RawTerm sourceScope) (subject classifier : RawTerm (sourceScope + 1)),
      ({ scope := sourceScope + 1, context := sourceContext.cons domain, subject := subject,
         classifier := classifier } : ElimObligation profile)
        ∈ rule.obligations profile sourceContext children levels carrier level flag →
      HasTypeUnion profile (targetContext.cons (RawTerm.subst substitution domain))
        (RawTerm.subst (iterateLiftRaw substitution 1) subject)
        (RawTerm.subst (iterateLiftRaw substitution 1) classifier)) :
    ∀ targetObligation ∈ rule.obligations profile targetContext
        (RawTermChildren.subst substitution children) levels
        (RawTerm.subst substitution carrier) level flag,
      HasTypeUnion profile targetObligation.context targetObligation.subject
        targetObligation.classifier := by
  cases rule with
  | baseType baseRule =>
      intro targetObligation targetMember
      cases targetMember
  | flat flatRule =>
      exact flatFormationObligations_pushSubst targetContext substitution flag children levels
        baseTypings
  | cumulative cumulativeRule =>
      exact cumulativeFormationObligations_pushSubst targetContext substitution flag
        children levels baseTypings crossingTypings
  | termIndexed termRule =>
      cases children with
      | childNil =>
          intro targetObligation targetMember
          cases targetMember
      | childCons carrierHead rest =>
          rename_i carrierShift _restShifts
          cases carrierShift with
          | zero =>
              intro targetObligation targetMember
              cases targetMember with
              | head =>
                  have carrierTyped := baseTypings carrierHead (universeCodeCell level flag)
                    (List.Mem.head _)
                  rwa [subst_universeCodeCell] at carrierTyped
              | tail _ tailMember =>
                  exact termIndexedEndpointObligations_pushSubst targetContext substitution carrier rest
                    (fun subject classifier member =>
                      baseTypings subject classifier (List.Mem.tail _ member))
                    targetObligation tailMember
          | succ _ =>
              intro targetObligation targetMember
              cases targetMember

/-! ## The RENAMING twins (the weakening consumer)

Identical spine recursion to the substitution push, with `RawRenaming` / `RawTerm.rename` /
`RawTermChildren.rename` / `rename_universeCodeCell` in place of their substitution counterparts. -/

/-- **The flat-family obligation RENAMING push** — the rename twin of `flatFormationObligations_pushSubst`. -/
theorem flatFormationObligations_pushRename {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (rawRenaming : FX1Poly.Tier0.Syntax.RawRenaming sourceScope targetScope) (flag : UniverseFlag) :
    ∀ {binderShifts : List Nat} (children : RawTermChildren binderShifts sourceScope)
      (levels : List LevelExpr),
      (∀ (subject classifier : RawTerm sourceScope),
        ({ scope := sourceScope, context := sourceContext, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ flatFormationObligations profile sourceContext flag children levels →
        HasTypeUnion profile targetContext (RawTerm.rename rawRenaming subject)
          (RawTerm.rename rawRenaming classifier)) →
      ∀ targetObligation ∈ flatFormationObligations profile targetContext flag
          (RawTermChildren.rename rawRenaming children) levels,
        HasTypeUnion profile targetObligation.context targetObligation.subject
          targetObligation.classifier := by
  intro binderShifts
  induction binderShifts with
  | nil =>
      intro children levels _sourceTypings targetObligation targetMember
      cases children
      cases targetMember
  | cons headShift restShifts ih =>
      intro children levels sourceTypings targetObligation targetMember
      cases children with
      | childCons childHead childTail =>
          cases headShift with
          | zero =>
              cases levels with
              | nil =>
                  -- LEVELS EXHAUSTED: the obligation list now FORCES the remaining children at `lzero`
                  -- (the rename twin of the subst push's exhausted-levels handling).
                  cases targetMember with
                  | head =>
                      have headTyped := sourceTypings childHead (universeCodeCell LevelExpr.lzero flag)
                        (List.Mem.head _)
                      rwa [rename_universeCodeCell] at headTyped
                  | tail _ tailMember =>
                      exact ih childTail []
                        (fun subject classifier member =>
                          sourceTypings subject classifier (List.Mem.tail _ member))
                        targetObligation tailMember
              | cons headLevel restLevels =>
                  cases targetMember with
                  | head =>
                      have headTyped := sourceTypings childHead (universeCodeCell headLevel flag)
                        (List.Mem.head _)
                      rwa [rename_universeCodeCell] at headTyped
                  | tail _ tailMember =>
                      exact ih childTail restLevels
                        (fun subject classifier member =>
                          sourceTypings subject classifier (List.Mem.tail _ member))
                        targetObligation tailMember
          | succ _ => cases targetMember

/-- **The term-indexed endpoint obligation RENAMING push** — the rename twin of
`termIndexedEndpointObligations_pushSubst`. -/
theorem termIndexedEndpointObligations_pushRename {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (rawRenaming : FX1Poly.Tier0.Syntax.RawRenaming sourceScope targetScope)
    (carrier : RawTerm sourceScope) :
    ∀ {shifts : List Nat} (children : RawTermChildren shifts sourceScope),
      (∀ (subject classifier : RawTerm sourceScope),
        ({ scope := sourceScope, context := sourceContext, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ termIndexedEndpointObligations profile sourceContext carrier children →
        HasTypeUnion profile targetContext (RawTerm.rename rawRenaming subject)
          (RawTerm.rename rawRenaming classifier)) →
      ∀ targetObligation ∈ termIndexedEndpointObligations profile targetContext
          (RawTerm.rename rawRenaming carrier) (RawTermChildren.rename rawRenaming children),
        HasTypeUnion profile targetObligation.context targetObligation.subject
          targetObligation.classifier := by
  intro shifts
  induction shifts with
  | nil =>
      intro children _sourceTypings targetObligation targetMember
      cases children
      cases targetMember
  | cons headShift restShifts ih =>
      intro children sourceTypings targetObligation targetMember
      cases children with
      | childCons childHead childTail =>
          cases headShift with
          | zero =>
              cases targetMember with
              | head =>
                  exact sourceTypings childHead carrier (List.Mem.head _)
              | tail _ tailMember =>
                  exact ih childTail
                    (fun subject classifier member =>
                      sourceTypings subject classifier (List.Mem.tail _ member))
                    targetObligation tailMember
          | succ _ => cases targetMember

/-- **The cumulative-family obligation RENAMING push** — the condition-agnostic rename twin of
`cumulativeFormationObligations_pushSubst`.  Same spine dispatch and same two-clause hypothesis:
`baseTypings` for the ambient-scope obligations, `crossingTypings` for the Π/Σ codomain at the LIFTED
renaming (`iterateLiftRaw rawRenaming 1`) and the renamed domain-extended target context. -/
theorem cumulativeFormationObligations_pushRename {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (rawRenaming : FX1Poly.Tier0.Syntax.RawRenaming sourceScope targetScope) (flag : UniverseFlag) :
    ∀ {binderShifts : List Nat} (children : RawTermChildren binderShifts sourceScope)
      (levels : List LevelExpr),
      (∀ (subject classifier : RawTerm sourceScope),
        ({ scope := sourceScope, context := sourceContext, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ cumulativeFormationObligations profile sourceContext flag children levels →
        HasTypeUnion profile targetContext (RawTerm.rename rawRenaming subject)
          (RawTerm.rename rawRenaming classifier)) →
      (∀ (domain : RawTerm sourceScope) (subject classifier : RawTerm (sourceScope + 1)),
        ({ scope := sourceScope + 1, context := sourceContext.cons domain, subject := subject,
           classifier := classifier } : ElimObligation profile)
          ∈ cumulativeFormationObligations profile sourceContext flag children levels →
        HasTypeUnion profile (targetContext.cons (RawTerm.rename rawRenaming domain))
          (RawTerm.rename (iterateLiftRaw rawRenaming 1) subject)
          (RawTerm.rename (iterateLiftRaw rawRenaming 1) classifier)) →
      ∀ targetObligation ∈ cumulativeFormationObligations profile targetContext flag
          (RawTermChildren.rename rawRenaming children) levels,
        HasTypeUnion profile targetObligation.context targetObligation.subject
          targetObligation.classifier := by
  intro binderShifts children levels baseTypings crossingTypings targetObligation targetMember
  match binderShifts, children, levels with
  | _, .childNil, _ => cases targetMember
  -- Element spine, levels exhausted: the FORCED `headChild : Type@0` obligation (cumulative free-`levels` fix).
  | _, .childCons (shift := 0) headChild .childNil, [] =>
      cases targetMember with
      | head =>
          have elementTyped := baseTypings headChild (universeCodeCell LevelExpr.lzero flag) (List.Mem.head _)
          rwa [rename_universeCodeCell] at elementTyped
      | tail _ tailMember => cases tailMember
  | _, .childCons (shift := 0) headChild .childNil, elementLevel :: _ =>
      cases targetMember with
      | head =>
          have elementTyped := baseTypings headChild (universeCodeCell elementLevel flag) (List.Mem.head _)
          rwa [rename_universeCodeCell] at elementTyped
      | tail _ tailMember => cases tailMember
  | _, .childCons (shift := 0) domain (.childCons (shift := 1) codomain .childNil),
      domainLevel :: codomainLevel :: _ =>
      cases targetMember with
      | head =>
          have domainTyped := baseTypings domain (universeCodeCell domainLevel flag) (List.Mem.head _)
          rwa [rename_universeCodeCell] at domainTyped
      | tail _ tailMember =>
          cases tailMember with
          | head =>
              have codomainTyped := crossingTypings domain codomain
                (universeCodeCell codomainLevel flag) (List.Mem.tail _ (List.Mem.head _))
              rwa [rename_universeCodeCell] at codomainTyped
          | tail _ deeperMember => cases deeperMember
  -- Π / Σ spine, levels exhausted / too short: the FORCED domain + codomain at `Type@0` (free-`levels` fix).
  | _, .childCons (shift := 0) domain (.childCons (shift := 1) codomain .childNil), [] =>
      cases targetMember with
      | head =>
          have domainTyped := baseTypings domain (universeCodeCell LevelExpr.lzero flag) (List.Mem.head _)
          rwa [rename_universeCodeCell] at domainTyped
      | tail _ tailMember =>
          cases tailMember with
          | head =>
              have codomainTyped := crossingTypings domain codomain
                (universeCodeCell LevelExpr.lzero flag) (List.Mem.tail _ (List.Mem.head _))
              rwa [rename_universeCodeCell] at codomainTyped
          | tail _ deeperMember => cases deeperMember
  | _, .childCons (shift := 0) domain (.childCons (shift := 1) codomain .childNil), [_] =>
      cases targetMember with
      | head =>
          have domainTyped := baseTypings domain (universeCodeCell LevelExpr.lzero flag) (List.Mem.head _)
          rwa [rename_universeCodeCell] at domainTyped
      | tail _ tailMember =>
          cases tailMember with
          | head =>
              have codomainTyped := crossingTypings domain codomain
                (universeCodeCell LevelExpr.lzero flag) (List.Mem.tail _ (List.Mem.head _))
              rwa [rename_universeCodeCell] at codomainTyped
          | tail _ deeperMember => cases deeperMember
  | _, .childCons (shift := 0) _ (.childCons (shift := 1) _ (.childCons _ _)), _ => cases targetMember
  | _, .childCons (shift := 0) _ (.childCons (shift := 0) _ _), _ => cases targetMember
  | _, .childCons (shift := 0) _ (.childCons (shift := _ + 2) _ _), _ => cases targetMember
  | _, .childCons (shift := _ + 1) _ _, _ => cases targetMember

/-- ★ **The unified formation-obligation RENAMING push** — the condition-agnostic rename twin of
`FormationRule.obligations_pushSubst`.  Same two-clause `baseTypings` / `crossingTypings` discipline; the
`cumulative` family routes through `cumulativeFormationObligations_pushRename` (binder-crossing codomain at
the lifted renaming). -/
theorem FormationRule.obligations_pushRename {profile : PolyProfile}
    {sourceScope targetScope : Nat} (rule : FormationRule)
    {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (rawRenaming : FX1Poly.Tier0.Syntax.RawRenaming sourceScope targetScope)
    {binderShifts : List Nat} (children : RawTermChildren binderShifts sourceScope)
    (levels : List LevelExpr) (carrier : RawTerm sourceScope) (level : LevelExpr) (flag : UniverseFlag)
    (baseTypings : ∀ (subject classifier : RawTerm sourceScope),
      ({ scope := sourceScope, context := sourceContext, subject := subject,
         classifier := classifier } : ElimObligation profile)
        ∈ rule.obligations profile sourceContext children levels carrier level flag →
      HasTypeUnion profile targetContext (RawTerm.rename rawRenaming subject)
        (RawTerm.rename rawRenaming classifier))
    (crossingTypings : ∀ (domain : RawTerm sourceScope) (subject classifier : RawTerm (sourceScope + 1)),
      ({ scope := sourceScope + 1, context := sourceContext.cons domain, subject := subject,
         classifier := classifier } : ElimObligation profile)
        ∈ rule.obligations profile sourceContext children levels carrier level flag →
      HasTypeUnion profile (targetContext.cons (RawTerm.rename rawRenaming domain))
        (RawTerm.rename (iterateLiftRaw rawRenaming 1) subject)
        (RawTerm.rename (iterateLiftRaw rawRenaming 1) classifier)) :
    ∀ targetObligation ∈ rule.obligations profile targetContext
        (RawTermChildren.rename rawRenaming children) levels
        (RawTerm.rename rawRenaming carrier) level flag,
      HasTypeUnion profile targetObligation.context targetObligation.subject
        targetObligation.classifier := by
  cases rule with
  | baseType baseRule =>
      intro targetObligation targetMember
      cases targetMember
  | flat flatRule =>
      exact flatFormationObligations_pushRename targetContext rawRenaming flag children levels
        baseTypings
  | cumulative cumulativeRule =>
      exact cumulativeFormationObligations_pushRename targetContext rawRenaming flag
        children levels baseTypings crossingTypings
  | termIndexed termRule =>
      cases children with
      | childNil =>
          intro targetObligation targetMember
          cases targetMember
      | childCons carrierHead rest =>
          rename_i carrierShift _restShifts
          cases carrierShift with
          | zero =>
              intro targetObligation targetMember
              cases targetMember with
              | head =>
                  have carrierTyped := baseTypings carrierHead (universeCodeCell level flag)
                    (List.Mem.head _)
                  rwa [rename_universeCodeCell] at carrierTyped
              | tail _ tailMember =>
                  exact termIndexedEndpointObligations_pushRename targetContext rawRenaming carrier rest
                    (fun subject classifier member =>
                      baseTypings subject classifier (List.Mem.tail _ member))
                    targetObligation tailMember
          | succ _ =>
              intro targetObligation targetMember
              cases targetMember

end FX1Poly.Typed
