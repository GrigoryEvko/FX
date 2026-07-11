import FX1Poly.Polygraph.Omega.CongruenceWithId
import FX1Poly.Polygraph.Omega.StrictAxioms
import FX1Poly.Polygraph.Omega.WalkingDistLawSortNF

/-! # Polygraph/Omega/WalkingStrongMonadPresentation — the walking strong monad as a SUB-PRESENTATION of
the walking distributive law (WP-STRONG r1, #2189)

★ **The walking strong monad `<c, t | eta_t, mu_t, st : c.t => t.c | monad + two strength rows>` re-encoded
as an `OmegaComputad` 2-polygraph.**  A strong monad (Kock 1972; Moggi, *Notions of computation and monads*,
Inf.&Comp. 93, 1991) is a monad `(T, eta, mu)` equipped with a tensorial strength
`st_{A,B} : A ⊗ TB → T(A ⊗ B)` natural in `A`, `B`, compatible with the monad's unit and multiplication.
Delooping a strict monoidal 2-category and reading `T` as an endo-1-cell `t` (with its monad `eta`, `mu`), the
tensoring object `A` as a BARE 1-cell `c` (NO monad structure — the whole point), and the strength as a 2-cell
`st : c.t => t.c`, this file ships FIVE generator labels and the `2 + 5 = 7` critical-pair rows.

## The adjudication — the strong monad IS the DISTLAW presentation minus the c-side monad structure

`WalkingDistLawPresentation.lean` presents the walking distributive law `swap : s.t => t.s` of a monad `S`
over a monad `T`: SEVEN generator labels (`s, t, eta_s, mu_s, eta_t, mu_t, swap`), FOURTEEN critical pairs
(four Beck + five S-monad-internal + five T-monad-internal).  Reading `s` as a BARE object `c` (dropping its
monad structure `eta_s`, `mu_s`) collapses that presentation to the walking strong monad, LAW BY LAW:

| Moggi/Kock strength law    | strict one-object reading                                       | DISTLAW correspondent | verdict |
|----------------------------|-----------------------------------------------------------------|-----------------------|---------|
| **S3** eta-strength        | `st . (c <| eta) = eta |> c`                                    | Beck-4 (swap × eta_t), s→c | SURVIVES |
| **S4** mu-strength         | `st . (c <| mu) = (st |> t).(t <| st).(mu |> c)`                | Beck-2 (swap × mu_t), s→c  | SURVIVES |
| **S1** unitor / rho        | `st` at `c = id` is an identity                                 | absorbed by strict units    | TRIVIALIZED (strictness) |
| **S2** associator / alpha  | composite-context strength = whisker-paste                      | absorbed by strict interchange | TRIVIALIZED (strictness) |
| —  (c-side mult compat)    | needs `mu_c`                                                    | Beck-1 (swap × mu_s)        | ABSENT (c has no mu_c) |
| —  (c-side unit compat)    | needs `eta_c`                                                   | Beck-3 (swap × eta_s)       | ABSENT (c has no eta_c) |

So the strong monad's generating 3-cells are the TWO surviving strength laws (Beck-2 & Beck-4 at the t-colour
with `c` a bare whiskering factor) plus the FIVE T-monad-internal rows: `2 + 5 = 7`, exactly DISTLAW's
fourteen minus Beck-1, Beck-3, and the five S-monad rows.  The five labels are DISTLAW's seven minus `eta_s`,
`mu_s`.  This drops GENERATORS (not merely axioms), so the c-side overlaps VANISH rather than orphan — the
census delta is coherence-preserving (recon (2)), machine-checked here as a count partition
(`strongMonadKeptDropPartitionsDistLawFourteen`).

## The negative self-attack — a c-side Beck axiom cannot even be FORMED (recon (4))

In the reduced signature `{c, t, eta, mu, st}` there is NO generator with a c-side monad shape (`mu_c : c.c => c`
or `eta_c : id => c`), so Beck-1 / Beck-3 cannot be STATED — `strength ⊊ distributive-law` unstatably, stronger
than "underivable".  The semantic countermodel (NAMED): every monad `T` on any monoidal category is canonically
strong for tensoring by an arbitrary object `A`, while `A` (= `c`) is generically NOT a monad — so strength holds
universally where Beck-1 / Beck-3 are false/meaningless.  Recorded by `fxStrong_cSideBeckAxiomsUnstatable` /
`fxStrong_strengthStrictlyWeakerThanDistLaw`.

## The honest scope (the recon caveats)

The single-`c` walker presents the FREE strong-monad theory over one generic tensoring object.  S1 / S2
trivialize because at a single generic object with strict units there is no `I⊗A` vs `A` nor `(A⊗B)⊗C` to
distinguish — exactly parallel to DISTLAW presenting the FREE distributive-law theory.  Naturality-in-`A` and
the multi-object associator coherence are model-side, not free-theory-presentation content — the same honesty
boundary DISTLAW holds.  The FULL decidable 2-cell word problem is walled at the two-colour monotone-map model
(same node as DISTLAW).  The 1-cell decision transports verbatim (B3).  The commutative monad (Kock) is a
SEPARATE follow-up walker (costrength + Kock agreement + braided base), NOT folded in (B4).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The single-object strong-monad signature (five generator labels) -/

/-- ★ The **five generator labels** of the walking strong monad: the bare context 1-generator `c` (the tensoring
object, NO monad structure), the endo-1-generator `t` (the monad), the monad unit `eta : id => t`, the monad
multiplication `mu : t.t => t`, and the tensorial strength `st : c.t => t.c`.  A finite inductive (full case
splits everywhere — the wildcard-`_ =>` propext leak is avoided).  Exactly DISTLAW's seven minus `eta_s`,
`mu_s` (the c-side monad structure). -/
inductive StrongMonadGenLabel where
  /-- The bare context 1-generator `c : * => *` (the tensoring object; NO monad structure). -/
  | contextColour
  /-- The endo-1-generator `t : * => *` (the monad). -/
  | endoColour
  /-- The monad unit `eta : id => t`. -/
  | unitEta
  /-- The monad multiplication `mu : t.t => t`. -/
  | multMu
  /-- The tensorial strength `st : c.t => t.c` — the interaction 2-cell, the star of the presentation. -/
  | strength

/-- The **integer tag** of a generator label — a full five-arm split (constant `Nat` motive, propext-free);
the label comparator compares tags. -/
def strongMonadLabelTag : StrongMonadGenLabel → Nat
  | .contextColour => 0
  | .endoColour => 1
  | .unitEta => 2
  | .multMu => 3
  | .strength => 4

/-- The **label `Bool` equality** — tags equal (`Nat.beq` on tags, propext-free); separates all five labels,
so the structural cell comparator distinguishes the context colour `c` from the endo colour `t`. -/
def strongMonadLabelBeq (labelA labelB : StrongMonadGenLabel) : Bool :=
  strongMonadLabelTag labelA == strongMonadLabelTag labelB

/-- ★ The **walking-strong-monad omega-computad**: one object (`Unit`), the constant five-label family
`StrongMonadGenLabel` at every dimension (the two 1-generators `c` / `t` and the three 2-generators are drawn
from it; globularity is extrinsic, so the label family need not know the cells its labels span).  Constant
family (no `Nat`-match in `genLabel`) — propext-clean. -/
def strongMonadOmegaComputad : OmegaComputad where
  modeCarrier := Unit
  genLabel := fun _ => StrongMonadGenLabel

/-- The trivial mode comparator (one object). -/
def strongMonadOmegaModeBeq :
    strongMonadOmegaComputad.modeCarrier → strongMonadOmegaComputad.modeCarrier → Bool :=
  fun _ _ => true

/-- The heterogeneous generator comparator — compares the five labels by tag (the two colours must be
separated, so this is NOT the trivial comparator the single-colour monad used). -/
def strongMonadOmegaGenBeq :
    (dimA dimB : Nat) →
      strongMonadOmegaComputad.genLabel dimA → strongMonadOmegaComputad.genLabel dimB → Bool :=
  fun _ _ labelA labelB => strongMonadLabelBeq labelA labelB

/-! ## The generators -/

/-- The single object `*`. -/
def strongMonadOmegaPoint : CellExpr strongMonadOmegaComputad 0 := CellExpr.ofMode ()

/-- ★ The **context** 1-generator `c : * => *` (the bare tensoring object). -/
def strongMonadContextGen : CellExpr strongMonadOmegaComputad 1 :=
  CellExpr.gen (dim := 0) StrongMonadGenLabel.contextColour strongMonadOmegaPoint strongMonadOmegaPoint

/-- ★ The **endo** 1-generator `t : * => *` (the monad). -/
def strongMonadEndoTGen : CellExpr strongMonadOmegaComputad 1 :=
  CellExpr.gen (dim := 0) StrongMonadGenLabel.endoColour strongMonadOmegaPoint strongMonadOmegaPoint

/-- The identity 1-cell `id` (the unit's source). -/
def strongMonadIdOne : CellExpr strongMonadOmegaComputad 1 := CellExpr.id strongMonadOmegaPoint

/-- The 1-cell word `c.t` (the strength's source). -/
def strongMonadCtWord : CellExpr strongMonadOmegaComputad 1 :=
  CellExpr.vcomp strongMonadContextGen strongMonadEndoTGen

/-- The 1-cell word `t.c` (the strength's target). -/
def strongMonadTcWord : CellExpr strongMonadOmegaComputad 1 :=
  CellExpr.vcomp strongMonadEndoTGen strongMonadContextGen

/-- The 1-cell word `t.t` (the `mu` source). -/
def strongMonadTtWord : CellExpr strongMonadOmegaComputad 1 :=
  CellExpr.vcomp strongMonadEndoTGen strongMonadEndoTGen

/-- ★ The monad **unit** `eta : id => t` (label `unitEta`). -/
def strongMonadEtaGen : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.gen (dim := 1) StrongMonadGenLabel.unitEta strongMonadIdOne strongMonadEndoTGen

/-- ★ The monad **multiplication** `mu : t.t => t` (label `multMu`). -/
def strongMonadMuGen : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.gen (dim := 1) StrongMonadGenLabel.multMu strongMonadTtWord strongMonadEndoTGen

/-- ★★ The **tensorial strength** `st : c.t => t.c` (label `strength`) — the interaction 2-cell, the star of
the presentation.  It is the DISTLAW swap `s.t => t.s` read at `s = c`. -/
def strongMonadStrengthGen : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.gen (dim := 1) StrongMonadGenLabel.strength strongMonadCtWord strongMonadTcWord

/-- The five generator labels, enumerated — the two 1-generators (`c`, `t`) + the three 2-generators
(`eta`, `mu`, `st`). -/
def allStrongMonadGenLabels : List StrongMonadGenLabel :=
  [.contextColour, .endoColour, .unitEta, .multMu, .strength]

/-- ★ **The generator-label count is exactly FIVE** — kernel-checked (`rfl`): the bare context 1-generator `c`,
the endo-1-generator `t`, and the THREE 2-cell generators (`eta`, `mu`, `st`).  Exactly DISTLAW's seven minus
`eta_s`, `mu_s` (the negative-self-attack anchor: there is NO c-side monad generator). -/
theorem strongMonadGeneratorLabelCountIsFive : allStrongMonadGenLabels.length = 5 := rfl

/-! # =========================================================================================
    # B1 — THE PRESENTATION: the two strength rows type-check on concrete words FIRST
    # =========================================================================================

★ **The two strength rows are re-instantiations of DISTLAW Beck-2 / Beck-4 at the t-colour with `c` a bare
whiskering factor** (recon: copy `distLawBeckTwoRightLeg` structure with s→c, do NOT re-derive by hand — the
S4 three-fold composite whisker order is the sole correctness risk).  Each leg is a `CellExpr
strongMonadOmegaComputad 2` that type-checks on the nose — the whiskerings and vertical composites elaborate
because the free carrier's composability is extrinsic.  This is the B1 truth-probe: the strength rows ARE
well-typed 2-cell equations on concrete words. -/

/-- ★ The **strength eta-law LEFT leg** `(c <| eta) . st : c.id => t.c` — Moggi's S3 in diagrammatic order
(DISTLAW Beck-4 left leg at s→c: `(s <| eta_t) . swap`). -/
def strongMonadStrengthEtaLeftLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft strongMonadContextGen strongMonadEtaGen) strongMonadStrengthGen

/-- ★ The **strength eta-law RIGHT leg** `eta |> c : id.c => t.c` — the S3 valley (DISTLAW Beck-4 right leg
at s→c: `eta_t |> s`). -/
def strongMonadStrengthEtaRightLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.whiskerRight strongMonadEtaGen strongMonadContextGen

/-- ★ The **strength mu-law LEFT leg** `(c <| mu) . st : c.(t.t) => t.c` — Moggi's S4 in diagrammatic order
(DISTLAW Beck-2 left leg at s→c: `(s <| mu_t) . swap`). -/
def strongMonadStrengthMuLeftLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft strongMonadContextGen strongMonadMuGen) strongMonadStrengthGen

/-- ★★ The **strength mu-law RIGHT leg** `(st |> t) . (t <| st) . (mu |> c) : (c.t).t => t.c` — the S4
three-fold composite (DISTLAW Beck-2 right leg at s→c: `(swap |> t) . (t <| swap) . (mu_t |> s)`; the whisker
order is the recon's flagged correctness risk, copied from `distLawBeckTwoRightLeg`). -/
def strongMonadStrengthMuRightLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight strongMonadStrengthGen strongMonadEndoTGen)
    (CellExpr.vcomp (CellExpr.whiskerLeft strongMonadEndoTGen strongMonadStrengthGen)
      (CellExpr.whiskerRight strongMonadMuGen strongMonadContextGen))

/-! ## The strength legs' boundary checks (the target valley is `t.c` on the nose) -/

/-- The strength eta-law left leg's target boundary is `t.c` (literal). -/
theorem strongMonadStrengthEtaLeftLeg_boundaryTarget :
    boundaryTarget strongMonadStrengthEtaLeftLeg = strongMonadTcWord := rfl

/-- The strength eta-law right leg's target boundary is `t.c` (literal) — both legs valley at `t.c`. -/
theorem strongMonadStrengthEtaRightLeg_boundaryTarget :
    boundaryTarget strongMonadStrengthEtaRightLeg = strongMonadTcWord := rfl

/-- The strength mu-law left leg's target boundary is `t.c` (literal). -/
theorem strongMonadStrengthMuLeftLeg_boundaryTarget :
    boundaryTarget strongMonadStrengthMuLeftLeg = strongMonadTcWord := rfl

/-- The strength mu-law right leg's target boundary is `t.c` (literal) — both legs valley at `t.c`. -/
theorem strongMonadStrengthMuRightLeg_boundaryTarget :
    boundaryTarget strongMonadStrengthMuRightLeg = strongMonadTcWord := rfl

/-! ## Non-vacuity — the strength legs are genuinely distinct 2-cells (the B1 truth-probe) -/

/-- ★ The strength eta-law legs are structurally DISTINCT (`(c <| eta).st` vs `eta |> c`). -/
theorem strongMonadStrengthEtaLegs_distinct :
    cellBeq strongMonadOmegaModeBeq strongMonadOmegaGenBeq
      strongMonadStrengthEtaLeftLeg strongMonadStrengthEtaRightLeg = false := rfl

/-- ★ The strength mu-law legs are structurally DISTINCT (`(c <| mu).st` vs the three-fold composite). -/
theorem strongMonadStrengthMuLegs_distinct :
    cellBeq strongMonadOmegaModeBeq strongMonadOmegaGenBeq
      strongMonadStrengthMuLeftLeg strongMonadStrengthMuRightLeg = false := rfl

/-- ★ **The two colours are genuinely distinct 1-cells** — `c.t` and `t.c` are structurally NOT equal (the
strength genuinely swaps context past the monad; the two-colour fact the single-ordinal model cannot represent). -/
theorem strongMonadCtTc_distinct :
    cellBeq strongMonadOmegaModeBeq strongMonadOmegaGenBeq
      strongMonadCtWord strongMonadTcWord = false := rfl

/-- ★ The **context and endo colours are genuinely distinct 1-generators** — `c` and `t` are structurally NOT
equal (the real tag comparator separates `contextColour` from `endoColour`). -/
theorem strongMonadContextEndo_distinct :
    cellBeq strongMonadOmegaModeBeq strongMonadOmegaGenBeq
      strongMonadContextGen strongMonadEndoTGen = false := rfl

/-- The strength eta-law leg SOURCE 1-cells `c.id` and `id.c` are structurally distinct (differ by the units),
so the peak join is genuinely modulo-strict (DISTLAW Beck-4 shape). -/
theorem strongMonadStrengthEtaLegs_notLiterallyParallelSource :
    cellBeq strongMonadOmegaModeBeq strongMonadOmegaGenBeq
      (boundarySource strongMonadStrengthEtaLeftLeg)
      (boundarySource strongMonadStrengthEtaRightLeg) = false := rfl

/-- The strength mu-law leg SOURCE 1-cells `c.(t.t)` and `(c.t).t` are structurally distinct (differ by one
associativity), so the peak join is genuinely modulo-strict (DISTLAW Beck-2 shape). -/
theorem strongMonadStrengthMuLegs_notLiterallyParallelSource :
    cellBeq strongMonadOmegaModeBeq strongMonadOmegaGenBeq
      (boundarySource strongMonadStrengthMuLeftLeg)
      (boundarySource strongMonadStrengthMuRightLeg) = false := rfl

/-! ## B1 non-vacuity probes (the truth-probe outputs) -/

#eval cellBeq strongMonadOmegaModeBeq strongMonadOmegaGenBeq
  strongMonadStrengthEtaLeftLeg strongMonadStrengthEtaRightLeg
#eval cellBeq strongMonadOmegaModeBeq strongMonadOmegaGenBeq
  strongMonadStrengthMuLeftLeg strongMonadStrengthMuRightLeg
#eval cellBeq strongMonadOmegaModeBeq strongMonadOmegaGenBeq strongMonadCtWord strongMonadTcWord
#eval allStrongMonadGenLabels.length

/-! ## B1 — the sub-presentation relationship to DISTLAW, machine-checked as a count partition

The strong monad drops DISTLAW's c-side GENERATORS (`eta_s`, `mu_s`) and hence its c-side critical pairs — a
COUNT PARTITION of DISTLAW's fourteen into the seven the strong monad KEEPS (the t-side: Beck-2, Beck-4, and
the five T-monad rows) and the seven it DROPS (the c-side: Beck-1, Beck-3, and the five S-monad rows).  A
direct `cellBeq` across the two computads is not type-correct (different label families), so the feasible
machine-checked comparison is the partition of `allDistLawCriticalPairs` and the count match against the strong
monad's seven. -/

/-- The **seven DISTLAW critical pairs the strong monad KEEPS** (the t-side): Beck-2 (`swap × mu_t`), Beck-4
(`swap × eta_t`) — the two strength rows — plus the five T-monad-internal rows. -/
def strongMonadKeptDistLawPairs : List DistLawCriticalPairLabel :=
  [.beckSwapMuT, .beckSwapEtaT,
    .monadTUnitUnit, .monadTLeftUnitAssoc, .monadTRightUnitAssoc, .monadTPentagon, .monadTRootUnitAssoc]

/-- The **seven DISTLAW critical pairs the strong monad DROPS** (the c-side): Beck-1 (`swap × mu_s`), Beck-3
(`swap × eta_s`) — needing the absent `mu_c` / `eta_c` — plus the five S-monad-internal rows.  They VANISH with
their generators (recon (2)), so no orphaned pair arises. -/
def strongMonadDroppedDistLawPairs : List DistLawCriticalPairLabel :=
  [.beckSwapMuS, .beckSwapEtaS,
    .monadSUnitUnit, .monadSLeftUnitAssoc, .monadSRightUnitAssoc, .monadSPentagon, .monadSRootUnitAssoc]

/-- ★★ **THE SUB-PRESENTATION PARTITION IS MACHINE-CHECKED.**  The strong monad's KEPT seven plus its DROPPED
seven exactly partition DISTLAW's fourteen critical pairs — `7 + 7 = 14`, kernel-checked (`rfl`).  This is the
count-level witness that the walking strong monad is the walking distributive law with the c-side monad
structure removed. -/
theorem strongMonadKeptDropPartitionsDistLawFourteen :
    strongMonadKeptDistLawPairs.length + strongMonadDroppedDistLawPairs.length
      = allDistLawCriticalPairs.length := rfl

/-! ## The B1 honesty markers -/

/-- ★ **ESTABLISHED (B1).**  The walking strong monad's two strength rows type-check on concrete words as
`CellExpr strongMonadOmegaComputad 2`: the eta-law `(c <| eta).st ~ eta |> c` (`strongMonadStrengthEtaLeftLeg`
/ `strongMonadStrengthEtaRightLeg`, DISTLAW Beck-4 at s→c) and the mu-law
`(c <| mu).st ~ (st |> t).(t <| st).(mu |> c)` (`strongMonadStrengthMuLeftLeg` /
`strongMonadStrengthMuRightLeg`, DISTLAW Beck-2 at s→c), both valley at `t.c` on the nose, the two colours
`c.t` / `t.c` genuinely distinct.  `= true`. -/
def fxStrong_strengthRowsTypeCheckOnConcreteWords : Bool := true

/-- ★ **THE SUB-PRESENTATION OF DISTLAW IS MACHINE-CHECKED (B1).**  `= true` records that the walking strong
monad is the walking distributive law minus the c-side monad structure, witnessed at the count level: the
seven kept critical pairs plus the seven dropped ones partition DISTLAW's fourteen
(`strongMonadKeptDropPartitionsDistLawFourteen`), and the label count is five = DISTLAW's seven minus `eta_s`,
`mu_s` (`strongMonadGeneratorLabelCountIsFive`). -/
def fxStrong_subPresentationOfDistLawMachineChecked : Bool := true

/-! # =========================================================================================
    # B2 — THE SEVEN CRITICAL-PAIR RESOLUTIONS (2 strength + 5 T-monad-internal)
    # =========================================================================================

★ **The walking strong monad = strength(st) + monad(mu, eta), single object, THREE 2-cell generators, SEVEN
critical-pair rows = 2 + 5.**  The two strength rows are the DISTLAW Beck-2 / Beck-4 shapes at the t-colour
with `c` a bare whiskering factor; the five T-monad rows reuse the walking monad's leg shapes verbatim
(the `MonadCoherentPresentation` five, at `t` / `eta` / `mu`).  All seven join modulo strict at peak and
valley, exactly as in DISTLAW: the strength rows peak by units (eta-law) / associativity (mu-law) and valley
at `t.c` by `refl`; the T-monad rows are the standard monad joins. -/

/-! ## The five T-monad-internal legs (over `t`, `eta`, `mu`) — the walking monad's five leg shapes -/

/-- **monad `unitUnit` left leg**: `eta |> t` (`id.t => t.t`). -/
def strongMonadMonadUnitUnitLeftLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.whiskerRight strongMonadEtaGen strongMonadEndoTGen

/-- **monad `unitUnit` right leg**: `t <| eta` (`t.id => t.t`). -/
def strongMonadMonadUnitUnitRightLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.whiskerLeft strongMonadEndoTGen strongMonadEtaGen

/-- **monad `leftUnitAssoc` left leg**: `mu |> t` (`(t.t).t => t.t`). -/
def strongMonadMonadLeftUnitAssocLeftLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.whiskerRight strongMonadMuGen strongMonadEndoTGen

/-- **monad `leftUnitAssoc` right leg**: `t <| mu` (`t.(t.t) => t.t`). -/
def strongMonadMonadLeftUnitAssocRightLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.whiskerLeft strongMonadEndoTGen strongMonadMuGen

/-- **monad `rightUnitAssoc` left leg**: `eta |> (t.t)` (`id.(t.t) => t.(t.t)`). -/
def strongMonadMonadRightUnitAssocLeftLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.whiskerRight strongMonadEtaGen strongMonadTtWord

/-- **monad `rightUnitAssoc` right leg**: `(t.t) <| eta` (`(t.t).id => (t.t).t`). -/
def strongMonadMonadRightUnitAssocRightLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.whiskerLeft strongMonadTtWord strongMonadEtaGen

/-- **monad `pentagon` left leg**: `(mu |> (t.t)) . (t <| mu)`. -/
def strongMonadMonadPentagonLeftLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight strongMonadMuGen strongMonadTtWord)
    (CellExpr.whiskerLeft strongMonadEndoTGen strongMonadMuGen)

/-- **monad `pentagon` right leg**: `((t.t) <| mu) . (mu |> t)`. -/
def strongMonadMonadPentagonRightLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft strongMonadTtWord strongMonadMuGen)
    (CellExpr.whiskerRight strongMonadMuGen strongMonadEndoTGen)

/-- **monad `rootUnitAssoc` left leg**: `(mu |> id) . (t <| eta)`. -/
def strongMonadMonadRootUnitAssocLeftLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight strongMonadMuGen strongMonadIdOne)
    (CellExpr.whiskerLeft strongMonadEndoTGen strongMonadEtaGen)

/-- **monad `rootUnitAssoc` right leg**: `((t.t) <| eta) . (mu |> t)`. -/
def strongMonadMonadRootUnitAssocRightLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft strongMonadTtWord strongMonadEtaGen)
    (CellExpr.whiskerRight strongMonadMuGen strongMonadEndoTGen)

/-! ## The seven critical-pair rows and the base relation -/

/-- ★ The **seven walking-strong-monad critical-pair rows** — the two strength rows (Beck-2 / Beck-4 at s→c)
and the five T-monad-internal rows.  A `CellRelOver` firing on each overlap's two reduction legs: the walking
strong monad's homotopy basis at Squier's convergent scope, the DISTLAW fourteen restricted to the t-side. -/
inductive StrongMonadCriticalRow :
    {d : Nat} → CellExpr strongMonadOmegaComputad d → CellExpr strongMonadOmegaComputad d → Prop where
  /-- Strength eta-law (Moggi S3, DISTLAW Beck-4 at s→c) — `(c <| eta).st ~ eta |> c`. -/
  | strengthEta : StrongMonadCriticalRow strongMonadStrengthEtaLeftLeg strongMonadStrengthEtaRightLeg
  /-- Strength mu-law (Moggi S4, DISTLAW Beck-2 at s→c) — `(c <| mu).st ~ (st |> t).(t <| st).(mu |> c)`. -/
  | strengthMu : StrongMonadCriticalRow strongMonadStrengthMuLeftLeg strongMonadStrengthMuRightLeg
  /-- monad `unitUnit`. -/
  | monadUnitUnit : StrongMonadCriticalRow strongMonadMonadUnitUnitLeftLeg strongMonadMonadUnitUnitRightLeg
  /-- monad `leftUnitAssoc`. -/
  | monadLeftUnitAssoc :
      StrongMonadCriticalRow strongMonadMonadLeftUnitAssocLeftLeg strongMonadMonadLeftUnitAssocRightLeg
  /-- monad `rightUnitAssoc`. -/
  | monadRightUnitAssoc :
      StrongMonadCriticalRow strongMonadMonadRightUnitAssocLeftLeg strongMonadMonadRightUnitAssocRightLeg
  /-- monad `pentagon`. -/
  | monadPentagon : StrongMonadCriticalRow strongMonadMonadPentagonLeftLeg strongMonadMonadPentagonRightLeg
  /-- monad `rootUnitAssoc`. -/
  | monadRootUnitAssoc :
      StrongMonadCriticalRow strongMonadMonadRootUnitAssocLeftLeg strongMonadMonadRootUnitAssocRightLeg

/-- The base relation the 3-cells resolve: the strict omega laws united with the seven critical-pair rows. -/
def strongMonadOmegaBaseRel : CellRelOver strongMonadOmegaComputad :=
  unionCellRel strongMonadOmegaComputad (StrictAxiomRel strongMonadOmegaComputad) StrongMonadCriticalRow

/-! ## The seven generating 3-cells -/

/-- ★★ **THE STRENGTH eta-law GENERATING 3-CELL** (Moggi S3). -/
def strongMonadStrengthEtaThreeCell :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      strongMonadStrengthEtaLeftLeg strongMonadStrengthEtaRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr StrongMonadCriticalRow.strengthEta)

/-- ★★ **THE STRENGTH mu-law GENERATING 3-CELL** (Moggi S4). -/
def strongMonadStrengthMuThreeCell :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      strongMonadStrengthMuLeftLeg strongMonadStrengthMuRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr StrongMonadCriticalRow.strengthMu)

/-- ★ **THE monad `unitUnit` GENERATING 3-CELL.** -/
def strongMonadMonadUnitUnitThreeCell :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      strongMonadMonadUnitUnitLeftLeg strongMonadMonadUnitUnitRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr StrongMonadCriticalRow.monadUnitUnit)

/-- ★ **THE monad `leftUnitAssoc` GENERATING 3-CELL.** -/
def strongMonadMonadLeftUnitAssocThreeCell :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      strongMonadMonadLeftUnitAssocLeftLeg strongMonadMonadLeftUnitAssocRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr StrongMonadCriticalRow.monadLeftUnitAssoc)

/-- ★ **THE monad `rightUnitAssoc` GENERATING 3-CELL.** -/
def strongMonadMonadRightUnitAssocThreeCell :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      strongMonadMonadRightUnitAssocLeftLeg strongMonadMonadRightUnitAssocRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr StrongMonadCriticalRow.monadRightUnitAssoc)

/-- ★ **THE monad `pentagon` GENERATING 3-CELL.** -/
def strongMonadMonadPentagonThreeCell :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      strongMonadMonadPentagonLeftLeg strongMonadMonadPentagonRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr StrongMonadCriticalRow.monadPentagon)

/-- ★ **THE monad `rootUnitAssoc` GENERATING 3-CELL.** -/
def strongMonadMonadRootUnitAssocThreeCell :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      strongMonadMonadRootUnitAssocLeftLeg strongMonadMonadRootUnitAssocRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr StrongMonadCriticalRow.monadRootUnitAssoc)

/-! ## The seven peak joins (the leg SOURCES join modulo strict) -/

/-- Strength eta-law peak: `c.id ~ id.c` through the common valley `c` (both units; DISTLAW Beck-4 peak). -/
def strongMonadStrengthEtaPeakJoin :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      (boundarySource strongMonadStrengthEtaLeftLeg) (boundarySource strongMonadStrengthEtaRightLeg) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitRight strongMonadContextGen)))
    (SaturatedConvOverWithId.symm
      (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft strongMonadContextGen))))

/-- Strength mu-law peak: `c.(t.t) ~ (c.t).t` by associativity (symm; DISTLAW Beck-2 peak). -/
def strongMonadStrengthMuPeakJoin :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      (boundarySource strongMonadStrengthMuLeftLeg) (boundarySource strongMonadStrengthMuRightLeg) :=
  SaturatedConvOverWithId.symm
    (SaturatedConvOverWithId.ofRelation
      (Or.inl (StrictAxiomRel.vcompAssoc strongMonadContextGen strongMonadEndoTGen strongMonadEndoTGen)))

/-- monad `unitUnit` peak: `id.t ~ t.id` (units). -/
def strongMonadMonadUnitUnitPeakJoin :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      (boundarySource strongMonadMonadUnitUnitLeftLeg) (boundarySource strongMonadMonadUnitUnitRightLeg) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft strongMonadEndoTGen)))
    (SaturatedConvOverWithId.symm
      (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitRight strongMonadEndoTGen))))

/-- monad `leftUnitAssoc` peak: `(t.t).t ~ t.(t.t)` (assoc). -/
def strongMonadMonadLeftUnitAssocPeakJoin :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      (boundarySource strongMonadMonadLeftUnitAssocLeftLeg)
      (boundarySource strongMonadMonadLeftUnitAssocRightLeg) :=
  SaturatedConvOverWithId.ofRelation
    (Or.inl (StrictAxiomRel.vcompAssoc strongMonadEndoTGen strongMonadEndoTGen strongMonadEndoTGen))

/-- monad `rightUnitAssoc` peak: `id.(t.t) ~ (t.t).id` (units). -/
def strongMonadMonadRightUnitAssocPeakJoin :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      (boundarySource strongMonadMonadRightUnitAssocLeftLeg)
      (boundarySource strongMonadMonadRightUnitAssocRightLeg) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft strongMonadTtWord)))
    (SaturatedConvOverWithId.symm
      (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitRight strongMonadTtWord))))

/-- monad `pentagon` peak: LITERALLY equal (`(t.t).(t.t)`) — `refl`. -/
def strongMonadMonadPentagonPeakJoin :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      (boundarySource strongMonadMonadPentagonLeftLeg)
      (boundarySource strongMonadMonadPentagonRightLeg) :=
  SaturatedConvOverWithId.refl _

/-- monad `rootUnitAssoc` peak: LITERALLY equal (`(t.t).id`) — `refl`. -/
def strongMonadMonadRootUnitAssocPeakJoin :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      (boundarySource strongMonadMonadRootUnitAssocLeftLeg)
      (boundarySource strongMonadMonadRootUnitAssocRightLeg) :=
  SaturatedConvOverWithId.refl _

/-! ## The seven valley joins (the leg TARGETS join modulo strict) -/

/-- Strength eta-law valley: both `t.c` — `refl`. -/
def strongMonadStrengthEtaValleyJoin :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      (boundaryTarget strongMonadStrengthEtaLeftLeg) (boundaryTarget strongMonadStrengthEtaRightLeg) :=
  SaturatedConvOverWithId.refl _

/-- Strength mu-law valley: both `t.c` — `refl`. -/
def strongMonadStrengthMuValleyJoin :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      (boundaryTarget strongMonadStrengthMuLeftLeg) (boundaryTarget strongMonadStrengthMuRightLeg) :=
  SaturatedConvOverWithId.refl _

/-- monad `unitUnit` valley: both `t.t` — `refl`. -/
def strongMonadMonadUnitUnitValleyJoin :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      (boundaryTarget strongMonadMonadUnitUnitLeftLeg) (boundaryTarget strongMonadMonadUnitUnitRightLeg) :=
  SaturatedConvOverWithId.refl _

/-- monad `leftUnitAssoc` valley: both `t.t` — `refl`. -/
def strongMonadMonadLeftUnitAssocValleyJoin :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      (boundaryTarget strongMonadMonadLeftUnitAssocLeftLeg)
      (boundaryTarget strongMonadMonadLeftUnitAssocRightLeg) :=
  SaturatedConvOverWithId.refl _

/-- monad `rightUnitAssoc` valley: `t.(t.t) ~ (t.t).t` (assoc). -/
def strongMonadMonadRightUnitAssocValleyJoin :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      (boundaryTarget strongMonadMonadRightUnitAssocLeftLeg)
      (boundaryTarget strongMonadMonadRightUnitAssocRightLeg) :=
  SaturatedConvOverWithId.symm
    (SaturatedConvOverWithId.ofRelation
      (Or.inl (StrictAxiomRel.vcompAssoc strongMonadEndoTGen strongMonadEndoTGen strongMonadEndoTGen)))

/-- monad `pentagon` valley: both `t.t` — `refl`. -/
def strongMonadMonadPentagonValleyJoin :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      (boundaryTarget strongMonadMonadPentagonLeftLeg) (boundaryTarget strongMonadMonadPentagonRightLeg) :=
  SaturatedConvOverWithId.refl _

/-- monad `rootUnitAssoc` valley: both `t.t` — `refl`. -/
def strongMonadMonadRootUnitAssocValleyJoin :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
      (boundaryTarget strongMonadMonadRootUnitAssocLeftLeg)
      (boundaryTarget strongMonadMonadRootUnitAssocRightLeg) :=
  SaturatedConvOverWithId.refl _

/-! ## The assembled per-pair resolution -/

/-- ★ A **coherent resolution** of one strong-monad critical pair, joinable MODULO the strict congruence: the
two leg SOURCES are convertible (peak), the two legs are convertible (the generating 3-cell), and the two leg
TARGETS are convertible (valley).  Parameterised by the two legs so all seven pairs share one datum shape. -/
structure StrongMonadCriticalPairResolved {d : Nat}
    (leftLeg rightLeg : CellExpr strongMonadOmegaComputad (d + 1)) : Prop where
  /-- The two leg SOURCES are convertible (the peak join). -/
  peakJoined : SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
    (boundarySource leftLeg) (boundarySource rightLeg)
  /-- The two legs are convertible (the generating 3-cell). -/
  legsConvertible :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel leftLeg rightLeg
  /-- The two leg TARGETS are convertible (the valley join). -/
  valleyJoined : SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
    (boundaryTarget leftLeg) (boundaryTarget rightLeg)

/-- ★★ The strength eta-law is coherently resolved (peak units, valley refl). -/
theorem strongMonadStrengthEtaResolved :
    StrongMonadCriticalPairResolved strongMonadStrengthEtaLeftLeg strongMonadStrengthEtaRightLeg :=
  ⟨strongMonadStrengthEtaPeakJoin, strongMonadStrengthEtaThreeCell, strongMonadStrengthEtaValleyJoin⟩

/-- ★★ The strength mu-law is coherently resolved (peak assoc, valley refl). -/
theorem strongMonadStrengthMuResolved :
    StrongMonadCriticalPairResolved strongMonadStrengthMuLeftLeg strongMonadStrengthMuRightLeg :=
  ⟨strongMonadStrengthMuPeakJoin, strongMonadStrengthMuThreeCell, strongMonadStrengthMuValleyJoin⟩

/-- The monad `unitUnit` pair is coherently resolved (peak units, valley refl). -/
theorem strongMonadMonadUnitUnitResolved :
    StrongMonadCriticalPairResolved strongMonadMonadUnitUnitLeftLeg strongMonadMonadUnitUnitRightLeg :=
  ⟨strongMonadMonadUnitUnitPeakJoin, strongMonadMonadUnitUnitThreeCell, strongMonadMonadUnitUnitValleyJoin⟩

/-- The monad `leftUnitAssoc` pair is coherently resolved (peak assoc, valley refl). -/
theorem strongMonadMonadLeftUnitAssocResolved :
    StrongMonadCriticalPairResolved strongMonadMonadLeftUnitAssocLeftLeg
      strongMonadMonadLeftUnitAssocRightLeg :=
  ⟨strongMonadMonadLeftUnitAssocPeakJoin, strongMonadMonadLeftUnitAssocThreeCell,
    strongMonadMonadLeftUnitAssocValleyJoin⟩

/-- The monad `rightUnitAssoc` pair is coherently resolved (peak units, valley assoc — the richest). -/
theorem strongMonadMonadRightUnitAssocResolved :
    StrongMonadCriticalPairResolved strongMonadMonadRightUnitAssocLeftLeg
      strongMonadMonadRightUnitAssocRightLeg :=
  ⟨strongMonadMonadRightUnitAssocPeakJoin, strongMonadMonadRightUnitAssocThreeCell,
    strongMonadMonadRightUnitAssocValleyJoin⟩

/-- The monad `pentagon` pair is coherently resolved (peak refl, valley refl — literally globular). -/
theorem strongMonadMonadPentagonResolved :
    StrongMonadCriticalPairResolved strongMonadMonadPentagonLeftLeg strongMonadMonadPentagonRightLeg :=
  ⟨strongMonadMonadPentagonPeakJoin, strongMonadMonadPentagonThreeCell, strongMonadMonadPentagonValleyJoin⟩

/-- The monad `rootUnitAssoc` pair is coherently resolved (peak refl, valley refl). -/
theorem strongMonadMonadRootUnitAssocResolved :
    StrongMonadCriticalPairResolved strongMonadMonadRootUnitAssocLeftLeg
      strongMonadMonadRootUnitAssocRightLeg :=
  ⟨strongMonadMonadRootUnitAssocPeakJoin, strongMonadMonadRootUnitAssocThreeCell,
    strongMonadMonadRootUnitAssocValleyJoin⟩

/-! ## The coherent-presentation bundle (the honest-scope statement) -/

/-- ★ **The walking-strong-monad coherent-presentation statement (honest scope).**  All SEVEN critical pairs
are coherently resolved modulo the strict congruence — a `Prop` conjunction of the seven per-pair resolutions
(2 strength + 5 T-monad). -/
def StrongMonadWalkerCoherentPresentationStatement : Prop :=
  StrongMonadCriticalPairResolved strongMonadStrengthEtaLeftLeg strongMonadStrengthEtaRightLeg ∧
  StrongMonadCriticalPairResolved strongMonadStrengthMuLeftLeg strongMonadStrengthMuRightLeg ∧
  StrongMonadCriticalPairResolved strongMonadMonadUnitUnitLeftLeg strongMonadMonadUnitUnitRightLeg ∧
  StrongMonadCriticalPairResolved strongMonadMonadLeftUnitAssocLeftLeg
    strongMonadMonadLeftUnitAssocRightLeg ∧
  StrongMonadCriticalPairResolved strongMonadMonadRightUnitAssocLeftLeg
    strongMonadMonadRightUnitAssocRightLeg ∧
  StrongMonadCriticalPairResolved strongMonadMonadPentagonLeftLeg strongMonadMonadPentagonRightLeg ∧
  StrongMonadCriticalPairResolved strongMonadMonadRootUnitAssocLeftLeg
    strongMonadMonadRootUnitAssocRightLeg

/-- ★★ **THE WALKING STRONG MONAD COHERENT PRESENTATION (seven critical pairs, joinable modulo strict).**  The
walking strong monad `<c, t | eta, mu, st | monad + two strength rows>` re-encoded as an `OmegaComputad`
2-polygraph has all SEVEN Squier critical pairs exhibited as generating 3-cells, each joinable-modulo-strict
at peak and valley — the two strength rows (Moggi S3 / S4, DISTLAW Beck-4 / Beck-2 at s→c) and the five
T-monad-internal rows. -/
theorem strongMonadWalkerCoherentPresentation : StrongMonadWalkerCoherentPresentationStatement :=
  ⟨strongMonadStrengthEtaResolved, strongMonadStrengthMuResolved, strongMonadMonadUnitUnitResolved,
    strongMonadMonadLeftUnitAssocResolved, strongMonadMonadRightUnitAssocResolved,
    strongMonadMonadPentagonResolved, strongMonadMonadRootUnitAssocResolved⟩

/-- ★ **The two-strength-rows statement (the genuinely-new content over the bare monad).**  A `Prop`
conjunction of the two strength coherent resolutions — the content that distinguishes the STRONG monad from
the bare monad (the tensorial strength's compatibility with the unit and multiplication). -/
def StrongMonadTwoStrengthRowsResolvedStatement : Prop :=
  StrongMonadCriticalPairResolved strongMonadStrengthEtaLeftLeg strongMonadStrengthEtaRightLeg ∧
  StrongMonadCriticalPairResolved strongMonadStrengthMuLeftLeg strongMonadStrengthMuRightLeg

/-- ★★ **THE TWO STRENGTH ROWS, COHERENTLY RESOLVED MODULO STRICT.**  Both strength-interaction critical pairs
exhibited as generating 3-cells, each joinable-modulo-strict at peak (units / associativity) and valley
(`t.c`, `refl`) — Moggi S3 / S4, the genuinely-new content of the walking strong monad over the bare monad. -/
theorem strongMonadTwoStrengthRowsResolved : StrongMonadTwoStrengthRowsResolvedStatement :=
  ⟨strongMonadStrengthEtaResolved, strongMonadStrengthMuResolved⟩

/-! ## The least-congruence universal property (map-out) -/

/-- ★ **THE SEVEN 3-CELLS GENERATE THE IDENTIFICATION (least-congruence UP).**  For any relation `targetRel`
absorbing the strong-monad base relation (a congruence containing the strict laws and the seven critical-pair
rows), the two legs of EVERY critical row are `targetRel`-related — so the seven generating 3-cells are the
datum whose fold through `SaturatedConvOverWithId.recInto` identifies each critical pair in EVERY model.
Uniform in the row (one statement covering all seven, keyed on `StrongMonadCriticalRow`). -/
theorem strongMonadCriticalPairsIdentifiedInEveryModel {targetRel : CellRelOver strongMonadOmegaComputad}
    (absorbs : IsSaturatedCongruenceWithId strongMonadOmegaComputad strongMonadOmegaBaseRel targetRel)
    {d : Nat} {leftLeg rightLeg : CellExpr strongMonadOmegaComputad d}
    (row : StrongMonadCriticalRow leftLeg rightLeg) : targetRel leftLeg rightLeg :=
  SaturatedConvOverWithId.recInto absorbs (SaturatedConvOverWithId.ofRelation (Or.inr row))

/-! ## The seven-row census -/

/-- The seven critical-pair labels — two strength, five T-monad-internal. -/
inductive StrongMonadCriticalPairLabel
  /-- Strength eta-law (Moggi S3). -/
  | strengthEta
  /-- Strength mu-law (Moggi S4). -/
  | strengthMu
  /-- monad `unitUnit`. -/
  | monadUnitUnit
  /-- monad `leftUnitAssoc`. -/
  | monadLeftUnitAssoc
  /-- monad `rightUnitAssoc`. -/
  | monadRightUnitAssoc
  /-- monad `pentagon`. -/
  | monadPentagon
  /-- monad `rootUnitAssoc`. -/
  | monadRootUnitAssoc

/-- The complete enumeration of the strong-monad critical pairs — SEVEN, listed. -/
def allStrongMonadCriticalPairs : List StrongMonadCriticalPairLabel :=
  [.strengthEta, .strengthMu,
    .monadUnitUnit, .monadLeftUnitAssoc, .monadRightUnitAssoc, .monadPentagon, .monadRootUnitAssoc]

/-- ★ **The critical-pair count is exactly SEVEN** — kernel-checked (`rfl`): 2 strength + 5 T-monad.  Exactly
DISTLAW's fourteen minus Beck-1, Beck-3, and the five S-monad rows. -/
theorem strongMonadCriticalPairCountIsSeven : allStrongMonadCriticalPairs.length = 7 := rfl

/-- The two strength-interaction labels — the genuinely-new content over the bare monad. -/
def allStrongMonadStrengthPairs : List StrongMonadCriticalPairLabel := [.strengthEta, .strengthMu]

/-- ★ **The strength-interaction count is exactly TWO** — kernel-checked (`rfl`): the Moggi S3 / S4 rows. -/
theorem strongMonadStrengthPairCountIsTwo : allStrongMonadStrengthPairs.length = 2 := rfl

/-- ★★ **THE KEPT-COUNT MATCHES THE STRONG-MONAD SEVEN.**  The seven DISTLAW critical pairs the strong monad
keeps (`strongMonadKeptDistLawPairs`) number exactly the strong monad's seven critical pairs
(`allStrongMonadCriticalPairs`) — the count-level sub-presentation correspondence (t-side of DISTLAW). -/
theorem strongMonadKeptMatchesStrongCount :
    strongMonadKeptDistLawPairs.length = allStrongMonadCriticalPairs.length := rfl

/-! ## B2 non-vacuity — a sample of monad legs are genuinely distinct 2-cells -/

/-- The monad `unitUnit` legs are structurally DISTINCT (`eta |> t` vs `t <| eta`). -/
theorem strongMonadMonadUnitUnitLegs_distinct :
    cellBeq strongMonadOmegaModeBeq strongMonadOmegaGenBeq
      strongMonadMonadUnitUnitLeftLeg strongMonadMonadUnitUnitRightLeg = false := rfl

/-- The monad `pentagon` legs are structurally DISTINCT (the two Godement whisker orders of `mu * mu`). -/
theorem strongMonadMonadPentagonLegs_distinct :
    cellBeq strongMonadOmegaModeBeq strongMonadOmegaGenBeq
      strongMonadMonadPentagonLeftLeg strongMonadMonadPentagonRightLeg = false := rfl

/-! ## B2 non-vacuity probes -/

#eval cellBeq strongMonadOmegaModeBeq strongMonadOmegaGenBeq
  strongMonadMonadUnitUnitLeftLeg strongMonadMonadUnitUnitRightLeg
#eval allStrongMonadCriticalPairs.length

/-- ★ **ESTABLISHED (B2).**  The walking strong monad's SEVEN Squier critical pairs (2 strength + 5 T-monad
transported) are exhibited as generating 3-cells over `strongMonadOmegaBaseRel`, each coherently resolved
modulo strict at peak and valley (`strongMonadWalkerCoherentPresentation`), with the seven-row census
(`strongMonadCriticalPairCountIsSeven`) and the least-congruence UP
(`strongMonadCriticalPairsIdentifiedInEveryModel`).  The two strength rows are the genuinely-new content over
the bare monad (`strongMonadTwoStrengthRowsResolved`).  `= true`. -/
def fxStrong_sevenCriticalPairsShipped : Bool := true

/-- ★ **THE TWO STRENGTH ROWS ARE DISTLAW BECK-2 AND BECK-4 (B2).**  `= true` records that the two strength
rows are exactly the DISTLAW Beck axioms surviving under s→c: the eta-law is Beck-4 (`swap × eta_t`, the S3
compatibility) and the mu-law is Beck-2 (`swap × mu_t`, the S4 compatibility), with `c` a bare whiskering
factor.  The c-side Beck-1 / Beck-3 are ABSENT (no `mu_c` / `eta_c` generator) — the negative self-attack. -/
def fxStrong_twoStrengthRowsAreBeckTwoAndFour : Bool := true

/-! # =========================================================================================
    # B3 — THE 1-CELL WORD PROBLEM DECISION, transported verbatim from DISTLAW (the Parikh transport)
    # =========================================================================================

★ **The strong monad's 1-cell theory IS the free commutative monoid on two letters — DISTLAW's `DistLawColour`
renamed `s ↦ c`.**  The strength's 1-cell shadow `c.t -> t.c` is the DISTLAW swap `s.t -> t.s` with only the
colour renamed, so the sorted normal form `t^m c^n`, inversion-count termination, orthogonal confluence, and
`conv ↔ sameCount` decision transport VERBATIM (recon (3): "no new mathematics at the 1-cell level").  This
section names the DISTLAW decision (`WalkingDistLawSortNF.lean`) under the colour bijection and exercises both
verdicts on concrete strong-monad words — the honest transport, not a re-derivation of the ~200-line sort. -/

/-- The **1-cell alphabet** of the walking strong monad: the two colours `c` (context) and `t` (endo).  Words
are `List StrongMonadColour`.  Two constructors — full case splits stay propext-clean. -/
inductive StrongMonadColour where
  /-- The context colour `c`. -/
  | contextLetter
  /-- The endo colour `t`. -/
  | endoLetter

/-- The **colour renaming** `c ↦ s`, `t ↦ t` onto DISTLAW's alphabet — the bijection under which the strong
monad's 1-cell theory IS the walking distributive law's. -/
def strongMonadColourToDistLaw : StrongMonadColour → DistLawColour
  | .contextLetter => DistLawColour.s
  | .endoLetter => DistLawColour.t

/-- Map a strong-monad word to its DISTLAW renaming — cons-only (no `List.map` / `List.append`, propext-clean),
so the transport reduces definitionally on concrete words. -/
def strongMonadWordToDistLaw : List StrongMonadColour → List DistLawColour
  | [] => []
  | colour :: rest => strongMonadColourToDistLaw colour :: strongMonadWordToDistLaw rest

/-- ★ The **strong monad's 1-cell word convertibility** — DISTLAW's swap-generated convertibility on the
renamed word.  Under the bijection `c ↦ s` this IS `DistLawWordConv`; the strength's 1-cell shadow
`c.t <-> t.c` is the DISTLAW swap `s.t <-> t.s`. -/
def StrongMonadWordConv (word1 word2 : List StrongMonadColour) : Prop :=
  DistLawWordConv (strongMonadWordToDistLaw word1) (strongMonadWordToDistLaw word2)

/-- ★ The **decision predicate**: two strong-monad words have equal letter counts (via the renaming).
Decidable, transported from DISTLAW. -/
def StrongMonadWordSameCount (word1 word2 : List StrongMonadColour) : Prop :=
  DistLawWordSameCount (strongMonadWordToDistLaw word1) (strongMonadWordToDistLaw word2)

/-- The decision predicate is decidable (transported from DISTLAW's `DistLawWordSameCount` instance). -/
instance (word1 word2 : List StrongMonadColour) : Decidable (StrongMonadWordSameCount word1 word2) :=
  inferInstanceAs (Decidable (DistLawWordSameCount _ _))

/-- ★★ **THE 1-CELL WORD PROBLEM DECISION (transported verbatim).**  Convertibility of strong-monad 1-cell
words under the strength-generated congruence is EQUIVALENT to same-letter-counts — a decidable predicate,
transported from DISTLAW's `distLawConv_iffSameCount` through the colour renaming.  The strong monad's 1-cell
theory is the free commutative monoid on `{c, t}` (Parikh-vector equality), the SAME object as DISTLAW's,
renamed. -/
theorem strongMonadConv_iffSameCount (word1 word2 : List StrongMonadColour) :
    StrongMonadWordConv word1 word2 ↔ StrongMonadWordSameCount word1 word2 :=
  distLawConv_iffSameCount (strongMonadWordToDistLaw word1) (strongMonadWordToDistLaw word2)

/-! ## Both verdicts on concrete strong-monad word pairs -/

/-- The word `c.t` (the strength's 1-cell source). -/
def strongMonadWordCt : List StrongMonadColour := [.contextLetter, .endoLetter]

/-- The word `t.c` (the strength's 1-cell target). -/
def strongMonadWordTc : List StrongMonadColour := [.endoLetter, .contextLetter]

/-- The word `c.c.t`. -/
def strongMonadWordCct : List StrongMonadColour := [.contextLetter, .contextLetter, .endoLetter]

/-- ★ **THE YES VERDICT** — `c.t` IS convertible to `t.c` (one strength swap).  Exercises the decision's
positive outcome on a concrete pair; under the renaming this is DISTLAW's `s.t ~ t.s`. -/
theorem strongMonadWordDecisionYes : StrongMonadWordConv strongMonadWordCt strongMonadWordTc :=
  DistLawWordConv.swapHere []

/-- ★ **THE NO VERDICT** — `c.c.t` is NOT convertible to `c.t` (different `c` counts, `2 != 1`).  Exercises
the decision's negative outcome; under the renaming this is DISTLAW's refuted `s.s.t` NOT `~ s.t`. -/
theorem strongMonadWordDecisionNo : ¬ StrongMonadWordConv strongMonadWordCct strongMonadWordCt :=
  fun hconv => distLawWordDecisionNo hconv

/-! ## The bridge to the presentation carrier (NAMED realization) -/

/-- Realize a colour as its 1-cell generator over the presentation computad. -/
def strongMonadColourGen : StrongMonadColour → CellExpr strongMonadOmegaComputad 1
  | .contextLetter => strongMonadContextGen
  | .endoLetter => strongMonadEndoTGen

/-- ★ **The bridge to the presentation carrier** — realize a `{c, t}`-word as a right-nested vertical composite
of colour generators (ending in the identity 1-cell).  Ties the transported combinatorial decision to the
`CellExpr strongMonadOmegaComputad 1` carrier; the strength 2-cell `strongMonadStrengthGen` realizes the swap
step on the canonical `c.t` / `t.c` (NAMED correspondence). -/
def strongMonadWordToCell : List StrongMonadColour → CellExpr strongMonadOmegaComputad 1
  | [] => strongMonadIdOne
  | colour :: rest => CellExpr.vcomp (strongMonadColourGen colour) (strongMonadWordToCell rest)

/-! ## B3 non-vacuity probes -/

#eval decide (StrongMonadWordSameCount strongMonadWordCt strongMonadWordTc)
#eval decide (StrongMonadWordSameCount strongMonadWordCct strongMonadWordCt)
#eval cellSize (strongMonadWordToCell strongMonadWordCt)

/-- ★ **ESTABLISHED (B3).**  The walking strong monad's 1-cell word problem is DECIDED by verbatim transport of
DISTLAW's Parikh decision under the colour renaming `c ↦ s`: convertibility under the strength-generated
congruence is equivalent to same-letter-counts (`strongMonadConv_iffSameCount`), a decidable predicate.  BOTH
verdicts are exercised on concrete word pairs — `strongMonadWordDecisionYes` (`c.t ~ t.c`) and
`strongMonadWordDecisionNo` (`c.c.t` NOT `~ c.t`).  The strong monad's 1-cell theory is the free commutative
monoid on `{c, t}` — the SAME object as DISTLAW's, renamed.  `= true`. -/
def fxStrong_oneCellWordProblemDecidedByParikhTransport : Bool := true

/-! # =========================================================================================
    # B4 — THE COMMUTATIVE LEDGER + the census-feed marker + the Moggi/effect-dimension tie-in
    # =========================================================================================

★ **The honest r1 scope: the STRENGTH is shipped; the COMMUTATIVE monad (Kock) is a SEPARATE follow-up walker,
NOT folded in (recon (6)).**  A commutative monad needs, over the strength `st : c.t => t.c`, ALSO a costrength
(right strength) and Kock's commutativity / agreement law `mu . T(st) . st' = mu . T(st') . st` — AND a
symmetric / braided monoidal base (a braiding generator with its own hexagon coherences).  The costrength is
NOT `st^{-1}` (opposite boundary but an independent 2-cell); the naive "other swap direction" reading is a
braiding, which is stronger.  This is genuinely NEW content (a materially bigger scaffold, the same
braided-structure territory as the Brauer / Frobenius-PROP lanes), recorded here as a ledger, not shipped.

## The Moggi / effect-dimension tie-in (fx_design §9, NAMED — docstring only, no cross-layer import)

FX's effect dimension (`fx_design.md` §1.1 dim 4, §6.3, §9) is a GRADED monad: an effect row `with E` is the
monadic modality under which a computation lives, and effect handlers (§9.6) are the algebra maps.  The
tensorial strength shipped here is exactly the structure that lets an effectful computation `T B` be tensored
with an ambient context `A` (the environment / the rest of the state) to give `T (A ⊗ B)` — i.e. the
strength is why `let`-sequencing threads the context through an effect (Moggi's computational lambda-calculus,
*Notions of computation and monads*, Inf.&Comp. 93, 1991; Kock, *Strong functors and monoidal monads*, Arch.
Math. 23, 1972).  This is the framing, NAMED; no `fx_design` layer is imported. -/

/-- ★ The **commutative-monad extension aspect** — which piece of the commutative-monad (Kock) theory it names:
the strength (shipped) or one of the three follow-up requirements (costrength, Kock agreement law, braided
base). -/
inductive StrongMonadCommutativeAspect where
  /-- The tensorial strength `st : c.t => t.c` (Moggi S3 / S4) — SHIPPED this round. -/
  | strengthShipped
  /-- The costrength (right strength) — a NEW independent generator, follow-up. -/
  | costrengthFollowUp
  /-- Kock's commutativity / agreement law `mu . T(st) . st' = mu . T(st') . st` — a NEW row, follow-up. -/
  | kockAgreementFollowUp
  /-- The symmetric / braided monoidal base (a braiding generator + hexagons) — a bigger scaffold, follow-up. -/
  | braidedBaseRequired

/-- ★ A **commutative-monad ledger entry** — one aspect of the Kock commutative-monad theory, a human-readable
description, and whether it is shipped THIS round (only the strength is). -/
structure StrongMonadCommutativeLedgerEntry where
  /-- Which aspect of the commutative-monad theory this entry names. -/
  aspect : StrongMonadCommutativeAspect
  /-- A human-readable description of the aspect. -/
  description : String
  /-- Whether this aspect is shipped in the r1 strong-monad round. -/
  shippedThisRound : Bool

/-- ★ The **commutative-monad follow-up ledger** — the strength shipped, and the three follow-up requirements
(costrength, Kock agreement, braided base) recorded as NOT shipped.  The honest record that the commutative
monad is a separate follow-up walker, not "strong + one row". -/
def strongMonadCommutativeLedger : List StrongMonadCommutativeLedgerEntry :=
  [ { aspect := .strengthShipped,
      description := "tensorial strength st : c.t => t.c (Moggi S3/S4) — SHIPPED (two strength rows resolved)",
      shippedThisRound := true },
    { aspect := .costrengthFollowUp,
      description := "costrength (right strength), an independent generator, NOT st inverse — follow-up",
      shippedThisRound := false },
    { aspect := .kockAgreementFollowUp,
      description := "Kock commutativity/agreement law mu.T(st).st' = mu.T(st').st — a new row, follow-up",
      shippedThisRound := false },
    { aspect := .braidedBaseRequired,
      description := "symmetric/braided monoidal base (braiding generator + hexagons) — follow-up scaffold",
      shippedThisRound := false } ]

/-- The commutative-monad ledger has exactly FOUR aspects (strength + three follow-ups). -/
theorem strongMonadCommutativeLedgerCountIsFour : strongMonadCommutativeLedger.length = 4 := rfl

/-- ★ **ONLY THE STRENGTH IS SHIPPED (machine-checked).**  The ledger's shipped flags are exactly
`[true, false, false, false]` — only the strength ships this round; the costrength, Kock agreement, and braided
base are follow-ups.  Kernel-checked (`rfl`) by folding the projection over the concrete ledger. -/
theorem strongMonadCommutativeLedger_onlyStrengthShipped :
    strongMonadCommutativeLedger.map (·.shippedThisRound) = [true, false, false, false] := rfl

/-- ★★ **THE SHIPPED SIDE IS GROUNDED.**  The commutative ledger's `strengthShipped = true` flag is not a bare
tally — it is grounded by the two strength rows actually resolved (`strongMonadTwoStrengthRowsResolved`), the
proof-carrying content behind the ledger's shipped entry. -/
theorem strongMonadCommutativeLedgerStrengthGrounded : StrongMonadTwoStrengthRowsResolvedStatement :=
  strongMonadTwoStrengthRowsResolved

/-! ## The B4 honesty markers -/

/-- ★ **THE COMMUTATIVE MONAD IS A SEPARATE FOLLOW-UP WALKER (B4).**  `= true` records that the walking
commutative monad (Kock) is NOT this round's deliverable and NOT "strong + one row": it needs a costrength
(independent generator), Kock's commutativity / agreement law, AND a symmetric / braided monoidal base — a
materially bigger scaffold (`strongMonadCommutativeLedger`, only the strength shipped).  Recorded, not
shipped. -/
def fxStrong_commutativeMonadSeparateFollowUp : Bool := true

/-- ★ **THE MOGGI / EFFECT-DIMENSION TIE-IN (fx_design §9, NAMED).**  `= true` records that the tensorial
strength shipped here is framed as the structure threading an ambient context through an effect — FX's effect
dimension (`fx_design.md` §1.1 dim 4 / §9) is a graded monad, and the strength is why `let`-sequencing carries
the environment past a computational effect (Moggi 1991; Kock 1972).  The framing is docstring-only; no
`fx_design` layer is imported (no cross-layer dependency). -/
def fxStrong_moggiEffectDimensionTieInNamed : Bool := true

/-- ★ **THE CENSUS FEED (recorded, applied additively in `SquierFamilyCensus`).**  `= true` records that the
single-object walking strong monad is a genuinely NEW single-object walker (five labels, seven critical pairs)
that FITS the `OmegaComputad` single-mode (`modeCarrier := Unit`) family pattern.  It is fed ADDITIVELY into
`SquierFamilyCensus` as a `SquierFamilyStrongWalker` entry (like WP-EQUIV / WP-FROBMONAD), WITHOUT touching the
decided-9 tally (`squierFamilyDecidedWalkerCountIsNine` keeps its name and meaning) — it is not one of the
decided-9 (its bare 2-cell decision is walled, same node as DISTLAW). -/
def fxStrong_censusFeedNewSingleObjectWalker : Bool := true

/-- ★ **THE C-SIDE BECK AXIOMS ARE UNSTATABLE (negative self-attack, recon (4)).**  `= true` records the
STRONG form of the sub-presentation claim: in the reduced signature `{c, t, eta, mu, st}` there is NO generator
with a c-side monad shape (`mu_c : c.c => c` or `eta_c : id => c`), so DISTLAW's Beck-1 (`swap × mu_s`) /
Beck-3 (`swap × eta_s`) cannot even be FORMED — their legs reference labels absent from `StrongMonadGenLabel`
(`strongMonadGeneratorLabelCountIsFive`: five labels, not seven).  This is stronger than "underivable". -/
def fxStrong_cSideBeckAxiomsUnstatable : Bool := true

/-- ★ **STRENGTH IS STRICTLY WEAKER THAN A DISTRIBUTIVE LAW (semantic countermodel, NAMED).**  `= true` records
the model-side asymmetry: every monad `T` on any monoidal category is canonically STRONG for tensoring by an
arbitrary object `A`, while `A` (= `c`) is generically NOT a monad — so strength (S3 / S4) holds universally
where DISTLAW's Beck-1 / Beck-3 (which require `A` itself to carry `eta_A`, `mu_A`) are false / meaningless.
`strength ⊊ distributive-law`; the strength set does not (and cannot) recover the c-side Beck axioms. -/
def fxStrong_strengthStrictlyWeakerThanDistLaw : Bool := true

/-! ## The B5 jam ledger — every wall the exact goal + a NAMED node -/

/-- ★ **JAM 1 — the full 2-cell decision (WALLED).**  Goal: decide EVERY parallel pair of free 2-cells (à la
`monadSaturatedTwoCellDecision`).  FALSE at this scope.  NAMED node: `monadPath_normalForm`
(`MonadSaturatedCanonReps.lean`) — "every 1-cell is a `t`-power" — is FALSE for the two colours `{c, t}` (`c.t`
is not a `t`-power), so the single-ordinal `List Nat` monotone-map model cannot encode an interleaved
`{c,t}`-word plus its shuffle data.  The SAME wall DISTLAW holds
(`fxDistLaw_fullTwoCellDecisionWalledAtTwoColourMonotoneMap`); the strong monad inherits it.  `= false`. -/
def fxStrong_fullTwoCellDecisionWalledAtTwoColourMonotoneMap : Bool := false

/-- ★ **JAM 2 — the commutative monad (FOLLOW-UP, not shipped).**  Goal: the walking commutative monad
(strength + costrength + Kock agreement + braided base).  NOT shipped this round.  NAMED nodes: the costrength
generator (independent of `st`), Kock's agreement row, and the symmetric / braided base (a braiding generator
with hexagon coherences — the same braided-structure territory as the Brauer / Frobenius-PROP lanes).  Recorded
in `strongMonadCommutativeLedger`.  `= false`. -/
def fxStrong_commutativeMonadFollowUpNotShipped : Bool := false

/-- ★ **JAM 3 — the full homotopy basis (OMEGA-5 HANDOFF).**  Goal: every parallel 2-path pair
3-cell-homotopic, by a structural length-fuel 2-path normalizer one dimension up.  NAMED node: the 2-path
normalizer over the seven-generator homotopy basis — the same OMEGA-5 remainder every walker deferred
(`fxDistLaw_fullHomotopyBasisReached`, `fxFrob_fullHomotopyBasisReached`).  The shipped content is the seven
generating 3-cells + their peak / valley joins, not the closure of every 2-sphere.  `= false`. -/
def fxStrong_fullHomotopyBasisReached : Bool := false

/-- ★★ **ESTABLISHED (r1 summary).**  The walking strong monad `<c, t | eta, mu, st | monad + two strength
rows>` re-encoded as an `OmegaComputad` 2-polygraph: FIVE generator labels, SEVEN critical-pair rows (2
strength = DISTLAW Beck-4 / Beck-2 at s→c + 5 T-monad transported), all coherently resolved modulo strict
(`strongMonadWalkerCoherentPresentation`), the least-congruence UP
(`strongMonadCriticalPairsIdentifiedInEveryModel`), a machine-checked sub-presentation partition of DISTLAW's
fourteen (`strongMonadKeptDropPartitionsDistLawFourteen`), and the 1-cell word problem decided by verbatim
Parikh transport (`strongMonadConv_iffSameCount`).  The commutative monad is a separate follow-up
(`strongMonadCommutativeLedger`); the full 2-cell decision and homotopy basis are walled / OMEGA-5.  `= true`. -/
def fxStrong_walkingStrongMonadPresentationShipped : Bool := true

end FX1Poly.Polygraph.Omega
