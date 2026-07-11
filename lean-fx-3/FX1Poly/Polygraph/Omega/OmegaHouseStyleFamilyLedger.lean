import FX1Poly.Polygraph.Omega.WalkingMonadOverQuotientAdjudication
import FX1Poly.Polygraph.Omega.WalkingStrongMonadOverQuotientAdjudication
import FX1Poly.Polygraph.Omega.WalkingDistLawOverQuotientAdjudication
import FX1Poly.Polygraph.Omega.InvolutionDemonstrator
import FX1Poly.Polygraph.Omega.CyclicThreeDemonstrator
import FX1Poly.Polygraph.Omega.IdempotentSemigroupDemonstrator
import FX1Poly.Polygraph.Omega.WalkingEquivalencePresentation

/-! # Polygraph/Omega/OmegaHouseStyleFamilyLedger — the family-wide house-style over-quotient census
(OMEGA HOUSE-STYLE SWEEP, WP-BI r4: B2 not-spurious + clean walkers, B4 homology family verdict, B5 the
censused bill)

★ **The family verdict, with the syntactic shape decidably separated from the semantic over-quotient.**  The
latent house-style defect is a critical-pair row whose two legs are BARE SINGLE WHISKERS of a lone generator
(`whiskerRight gen colour` vs `whiskerLeft colour gen`) — the shape the walking monad, strong monad and
distributive law over-quotient on.  This file ships the machine-checked family classification:

  * a DECIDABLE structural predicate `isBareGenWhisker` detecting the syntactic shape;
  * proof that the shape is PRESENT in the monad / strong-monad / distlaw (SHIPPED over-quotients),
    involution / cyclic-3 / idempotent (SHAPE-MATCHES, over-quotient status UNRESOLVED — model-dependent),
    and ABSENT in the walking equivalence (the positive house-style-correct example);
  * the honest classification: syntactic-shape-present is NECESSARY but NOT SUFFICIENT for over-quotient — the
    monad family is confirmed by the faithful `Mat(N)`-monoid model, but the torsion / idempotent trio is
    UNRESOLVED (their faithful models are group-like / coherent and are PREDICTED to IDENTIFY the legs — no
    over-quotient claim is made);
  * the homology no-impact family verdict (the shipped per-walker abelianization-invisibility, consolidated,
    plus the NAME-ONLY cross-lane flag for the Homology lane);
  * the censused r4-bill (Frobenius, the trio's faithful models, the equivalence positive example).

## The discriminant (why the monad over-quotients but the involution is predicted clean)

The walking monad's faithful model is the augmented simplex Delta (monotone maps): `eta` = coface, `mu` =
codegeneracy, and `delta_0 = eta |> t` != `delta_1 = t <| eta` are DISTINCT monotone maps — parallel but not
equal, so the bare-whisker row genuinely over-quotients (machine-confirmed here via the faithful `Mat(N)`
monoid).  The involution / cyclic-3 make the generator TORSION (`s^2 = id` / `s^3 = id`), so the faithful model
is a delooped finite group — 2-coherent, all parallel 2-cells collapse — and the bare-whisker legs are PREDICTED
to AGREE (a clean walker).  A `Mat(N)` separation is worthless there: `Mat(N)`'s generator is NOT invertible, so
it is not a faithful model of a torsion walker.  Hence NO over-quotient is claimed for the trio; the honest
status is UNRESOLVED pending the faithful group / idempotent model (the NAMED r4-bill wall).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! # =========================================================================================
    # B2 — THE DECIDABLE SYNTACTIC-SHAPE PREDICATE (the latent-shape detector)
    # ========================================================================================= -/

/-- Whether a cell's **head constructor is a bare generator** — a total full-enum fold (the `cellSize` idiom,
propext-clean), true only for `.gen`.  Used to detect a lone-generator whiskered cell. -/
def isGenHead {computad : OmegaComputad} : {dim : Nat} → CellExpr computad dim → Bool
  | _, .ofMode _ => false
  | _, .gen _ _ _ => true
  | _, .id _ => false
  | _, .vcomp _ _ => false
  | _, .whiskerLeft _ _ => false
  | _, .whiskerRight _ _ => false

/-- ★ Whether a 2-cell has the **bare single-whisker-of-a-lone-generator shape** — `whiskerRight (gen ..) _`
or `whiskerLeft _ (gen ..)`.  A total full-enum fold (propext-clean); this is the decidable detector of the
latent house-style shape (the leg form the monad family over-quotients on).  NECESSARY for over-quotient, NOT
sufficient (the faithful model still decides). -/
def isBareGenWhisker {computad : OmegaComputad} : {dim : Nat} → CellExpr computad dim → Bool
  | _, .ofMode _ => false
  | _, .gen _ _ _ => false
  | _, .id _ => false
  | _, .vcomp _ _ => false
  | _, .whiskerLeft _ innerCell => isGenHead innerCell
  | _, .whiskerRight innerCell _ => isGenHead innerCell

/-! # =========================================================================================
    # B2 — SHAPE PRESENT: the SHIPPED over-quotients (monad / strong / distlaw)
    # ========================================================================================= -/

/-- The walking monad's `unitUnit` legs BOTH carry the bare-gen-whisker shape (`eta |> t` and `t <| eta`). -/
theorem omegaHouseStyleMonadUnitUnitLegsAreBareWhiskers :
    isBareGenWhisker monadOmegaUnitUnitLeftLeg = true
      ∧ isBareGenWhisker monadOmegaUnitUnitRightLeg = true := ⟨rfl, rfl⟩

/-- The strong monad's T-monad `unitUnit` legs carry the bare-gen-whisker shape. -/
theorem omegaHouseStyleStrongUnitUnitLegsAreBareWhiskers :
    isBareGenWhisker strongMonadMonadUnitUnitLeftLeg = true
      ∧ isBareGenWhisker strongMonadMonadUnitUnitRightLeg = true := ⟨rfl, rfl⟩

/-- The distributive law's `monadS unitUnit` legs carry the bare-gen-whisker shape. -/
theorem omegaHouseStyleDistLawMonadSUnitUnitLegsAreBareWhiskers :
    isBareGenWhisker (distLawUnitUnitLeftLegOf distLawSGen distLawEtaSGen) = true
      ∧ isBareGenWhisker (distLawUnitUnitRightLegOf distLawSGen distLawEtaSGen) = true := ⟨rfl, rfl⟩

/-! # =========================================================================================
    # B2 — SHAPE PRESENT but OVER-QUOTIENT UNRESOLVED: the not-spurious trio (torsion / idempotent)
    # =========================================================================================

★ **Shape matches, classification model-dependent — NO over-quotient claimed.**  The involution `sss`, cyclic-3
`ssss` / `sssss` and idempotent `eee` legs are bare-gen-whiskers (machine-checked below), the SAME syntactic
shape as the monad.  But their generators are TORSION (`s^2 = id`, `s^3 = id`) or IDEMPOTENT (`e^2 = e`), whose
faithful models are group-like / coherent and PREDICT the legs AGREE — a clean walker.  `Mat(N)` cannot decide:
its generator is non-invertible / non-idempotent, so a `Mat(N)` separation would be UNFAITHFUL.  The over-quotient
status is UNRESOLVED (r4-bill: build the faithful group / idempotent model). -/

/-- The involution `sss` legs carry the bare-gen-whisker shape (`rho |> s` and `s <| rho`). -/
theorem omegaHouseStyleInvolutionSssLegsAreBareWhiskers :
    isBareGenWhisker involutionLeftLeg = true ∧ isBareGenWhisker involutionRightLeg = true := ⟨rfl, rfl⟩

/-- The cyclic-3 `ssss` and `sssss` legs carry the bare-gen-whisker shape. -/
theorem omegaHouseStyleCyclicThreeLegsAreBareWhiskers :
    isBareGenWhisker cyclicThreeOmegaSsssLeftLeg = true
      ∧ isBareGenWhisker cyclicThreeOmegaSsssRightLeg = true
      ∧ isBareGenWhisker cyclicThreeOmegaSssssLeftLeg = true
      ∧ isBareGenWhisker cyclicThreeOmegaSssssRightLeg = true := ⟨rfl, rfl, rfl, rfl⟩

/-- The idempotent-semigroup `eee` legs carry the bare-gen-whisker shape (`mu |> e` and `e <| mu`). -/
theorem omegaHouseStyleIdempotentEeeLegsAreBareWhiskers :
    isBareGenWhisker idempotentSemigroupOmegaEeeLeftLeg = true
      ∧ isBareGenWhisker idempotentSemigroupOmegaEeeRightLeg = true := ⟨rfl, rfl⟩

/-! # =========================================================================================
    # B2 — SHAPE ABSENT: the walking equivalence (the positive house-style-correct example)
    # =========================================================================================

★ **The latent shape does NOT arise — the house-style-correct walker.**  The walking equivalence states every
row at a CLOSED composite landing on an identity (cancellation `eta.etaInv ~ id_A`, triangle
`(eta|>f).(f<|eps) ~ id_f`), never at a bare whisker.  Machine-checked: none of its legs is a bare-gen-whisker
(they are vertical composites or identities).  This is exactly what the defective walkers SHOULD have done —
post-compose the two whisker legs so the row lands on a genuine law. -/

/-- The equivalence's cancellation row relates a COMPOSITE (`eta . etaInv`, a `vcomp`) to an IDENTITY (`id_A`) —
NEITHER is a bare-gen-whisker. -/
theorem omegaHouseStyleEquivCancellationLegsAreNotBareWhiskers :
    isBareGenWhisker walkingEquivEtaEtaInv = false ∧ isBareGenWhisker walkingEquivIdIdA = false := ⟨rfl, rfl⟩

/-- The equivalence's triangle row relates a COMPOSITE (`(eta|>f).(f<|eps)`, a `vcomp`) to an IDENTITY
(`id_f`) — NEITHER is a bare-gen-whisker.  The latent shape is structurally ABSENT. -/
theorem omegaHouseStyleEquivTriangleLegsAreNotBareWhiskers :
    isBareGenWhisker walkingEquivLeftTriangleLeg = false ∧ isBareGenWhisker walkingEquivIdF = false := ⟨rfl, rfl⟩

/-! ## The B2 non-vacuity probes -/

#eval isBareGenWhisker monadOmegaUnitUnitLeftLeg
#eval isBareGenWhisker involutionLeftLeg
#eval isBareGenWhisker walkingEquivEtaEtaInv
#eval isBareGenWhisker walkingEquivLeftTriangleLeg

/-! # =========================================================================================
    # B2 / B4 / B5 — THE FAMILY LEDGER MARKERS
    # ========================================================================================= -/

/-- ★★ **THE FAMILY OVER-QUOTIENT PATTERN — THREE walkers machine-confirmed (12 rows).**  `= true` records the
three shipped adjudications: the walking monad (3 bare-whisker rows), the walking strong monad (3 T-monad rows),
and the walking distributive law (6 monad-internal rows, three per colour) all over-quotient their r1
presentation on the bare-single-whisker-commute rows, each separated by a faithful `Mat(N)`-monoid model and
each restored to a sound genuine-law sub-theory.  The bunched-bimonoid r3 was the fourth (the m-side is this
walking monad transported).  The syntactic shape is decidably present
(`omegaHouseStyle{Monad,Strong,DistLawMonadS}UnitUnitLegsAreBareWhiskers`). -/
def fxOmegaHouseStyle_familyThreeWalkersOverQuotientConfirmed : Bool := true

/-- ★★ **THE NOT-SPURIOUS TRIO — shape matches, over-quotient UNRESOLVED (model-dependent, PREDICTED CLEAN).**
`= true` records the honest classification: the involution `sss`, cyclic-3 `ssss` / `sssss`, and idempotent
`eee` legs carry the bare-gen-whisker shape
(`omegaHouseStyle{Involution,CyclicThree,Idempotent}...LegsAreBareWhiskers`) — the SAME syntactic shape as the
monad — but their generators are torsion (`s^2 = id`, `s^3 = id`) / idempotent (`e^2 = e`), whose faithful models
are group-like / coherent and PREDICT the two legs AGREE (a clean walker).  NO over-quotient is claimed: a
`Mat(N)` separation would be UNFAITHFUL (its generator is not invertible / idempotent).  The classification is
UNRESOLVED pending the faithful group / idempotent model (the r4-bill wall). -/
def fxOmegaHouseStyle_notSpuriousTrioShapeMatchesOverQuotientUnresolved : Bool := true

/-- ★★ **THE DISCRIMINANT — syntactic shape is NECESSARY, NOT SUFFICIENT, for over-quotient.**  `= true`
records that `isBareGenWhisker` decides the syntactic shape but the FAITHFUL MODEL decides the over-quotient:
the monad family's Delta (monotone maps) has DISTINCT parallel cofaces (`delta_0 != delta_1`, separates), the
torsion trio's delooped group is 2-coherent (parallel 2-cells collapse, identifies).  The `Mat(N)` monoid is a
faithful separator ONLY for the non-invertible monad family; for a torsion / idempotent walker it is unfaithful.
So over-quotient = (shape present) AND (faithful model separates) — machine-confirmed for three walkers,
UNRESOLVED for the trio. -/
def fxOmegaHouseStyle_shapeIsNecessaryNotSufficientFaithfulModelDecides : Bool := true

/-- ★★ **THE POSITIVE EXAMPLE — the walking equivalence is house-style-correct (shape ABSENT).**  `= true`
records `omegaHouseStyleEquiv{Cancellation,Triangle}LegsAreNotBareWhiskers`: the equivalence states every row at
a closed composite landing on an identity (cancellation, triangle), never at a bare whisker, so the latent shape
is structurally ABSENT.  This is the correct house style the defective walkers should have followed — the
positive census entry (no separation, no over-quotient, no residual). -/
def fxOmegaHouseStyle_walkingEquivalenceIsPositiveExampleShapeAbsent : Bool := true

/-- ★★ **THE HOMOLOGY FAMILY VERDICT (in-lane): NO IMPACT — the over-quotient rows are abelianization-invisible
for every shipped walker.**  `= true` records the consolidation of the shipped per-walker no-impact witnesses
(`{monad,strong,distLaw}OmegaOverQuotientRowsAbelianizationEqual`): every over-quotient row's two legs carry
EQUAL abelianized generator counts (they differ only in whisker POSITION, which abelianization forgets), so the
H2-WALKERS chain-complex boundary maps `d2` / `d3` (abelianized counts) do not distinguish the legs.  The
over-quotient is a CONGRUENCE-level fact, invisible to abelianization; the homology is untouched. -/
def fxOmegaHouseStyle_homologyFamilyNoImpactAbelianizationInvisible : Bool := true

/-- ★ **CROSS-LANE FLAG (NAME only) — the H2-WALKERS homology is untouched by the family over-quotient audit.**
`= true` records, for the Homology lane owner: the family over-quotient rows are abelianization-invisible (their
cofork columns are position-blind — cf. `monadOmegaCriticalPairCoforkColumn unitUnit = (0,0)`), so the shipped
`WalkerChainComplex` / H2 computations are UNCHANGED by this audit.  The ONLY operation that could recompute H2
is a user-gated row RETRACTION (dropping rows from the critical-pair list), which is a presentation edit the
Homology lane owns independently — NOT performed here.  NAME-ONLY: cross-lane (`Polygraph/Homology`); flagged
for its owner, not edited. -/
def fxOmegaHouseStyle_homologyLaneUntouchedRetractionUserGatedFlag : Bool := true

/-- ★ **THE CENSUSED r4-BILL — the un-shipped walkers, honestly deferred.**  `= false` records the remaining
work: (1) FROBENIUS (6 latent rows — needs a genuine Frobenius / planar-2Cob model; `Mat(N)` is UNVERIFIED for
the Frobenius laws F1/F2 and imposes commutativity on a non-commutative walker, so a `Mat(N)` separation would be
worthless); (2) the NOT-SPURIOUS TRIO's faithful group / idempotent models (to decide identify-vs-separate — the
prediction is identify / CLEAN); (3) the walking co-monad / co-KZ op-duals (transport the monad separation
through `opCellExpr` — cheap follow-on); (4) full isolation over `StrictAxiomRel union SoundRow` for each shipped
walker (the matMul-associativity Fubini kit); (5) matrix completeness (the spider NF) per walker.  Each NAMED at
its node. -/
def fxOmegaHouseStyle_censusedBillFrobeniusTrioModelsOpDualsFubini : Bool := false

/-- ★ **ESTABLISHED (B5) — the family house-style over-quotient census ledger.**  `= true` records the family
scoreboard: THREE walkers machine-confirmed over-quotient (monad / strong / distlaw, 12 rows, each `Mat(N)`-
separated + sound-sub-theory-restored + decision-re-audited-clean + homology-no-impact); the NOT-SPURIOUS trio
(involution / cyclic-3 / idempotent) shape-matched but over-quotient-UNRESOLVED (predicted clean, no claim); the
walking equivalence the POSITIVE example (shape absent); the homology family verdict NO IMPACT (cross-lane flag
NAME-only); the r4-bill censused (Frobenius, the trio's faithful models, the op-duals, the Fubini isolation, the
spider completeness).  Every wall NAMED at its node. -/
def fxOmegaHouseStyle_familyOverQuotientCensusLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
