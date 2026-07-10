import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadCanonicalWord
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWhiskerRightMult
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeCell
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadSeed

/-! # WalkingIdempotent/IdempotentSaturatedReps — the conv-FREE boundary-normalizer skeleton (bespoke-free)
(POLY-TAB r5 retirement, PORT-IN skeleton)

The conv-FREE representatives and their `Nat` / path / `Eq` support lemmas the native r4 lane
(`IdempotentSaturated{MuInvertible,Ladder,GeneralBricks,RightWhisker,Normalizer}`) consumes IN CODE, relocated
VERBATIM (no re-proof) OUT of the retiring bespoke normalizer chain
(`IdempotentMonad{MuInvertible,Normalizer,GeneralNormalizer,RightWhisker,FullNormalizer}`) into this bespoke-free
home.  Every declaration here is a `RawTwoCellExpr` construction (`growTower`, `canonThroughT`, `mulThenUnitRightWhisker`,
`godementUnitMul`, `repNF`, `repFull`), a boundary-length `Nat` / `composePath` lemma, or an `Eq` on free cells —
NONE mentions the bespoke `IdempotentMonadSaturatedTwoCellConv` (the conv-PRODUCING theorems stay reproved as `*Gen`
twins over `SaturatedConvOver monadModeSignature IdempotentLawRel` in the native files).  It imports only the
walking-monad substrate (`MonadCanonicalWord` / `MonadWhiskerRightMult` / `MonadNormalizeCell`) plus the idempotence
faces (`IdempotentMonadSeed`), so it is entirely off the retired chain.

Raw Lean 4 + Init; STRUCTURAL `Nat` recursion + `cases` on free boundary equalities.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## Cell-level rigidity: no free 2-cell collapses `t^{m+1}` to the identity 1-cell -/

private theorem natSumZero {firstAddend secondAddend : Nat}
    (hFirst : firstAddend = 0) (hSecond : secondAddend = 0) : firstAddend + secondAddend = 0 := by
  rw [hFirst, hSecond]

/-- ★ **Cell-level rigidity ("no `1 ⇒ 0`").**  Every free 2-cell of the walking idempotent monad whose TARGET
1-cell has length `0` (the identity `t^0 = nil`) has a SOURCE 1-cell of length `0`.  Structural induction over
`RawTwoCellExpr`: the two generators `eta`/`mu` both target `t` (length `1`, vacuous); `id` copies the boundary;
`vcomp` threads the two factors; the whiskerings split the length by `ModalityPath.length_composePath`. -/
theorem rawCell_targetLenZero_impliesSourceLenZero :
    {sourceMode targetMode : MonadMode} →
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) →
    targetPath.length = 0 → sourcePath.length = 0
  | _, _, _, _, .gen MonadTwoCell.eta, hlen => Nat.noConfusion hlen
  | _, _, _, _, .gen MonadTwoCell.mu, hlen => Nat.noConfusion hlen
  | _, _, _, _, .id _, hlen => hlen
  | _, _, _, _, .vcomp cellLower cellUpper, hlen =>
      rawCell_targetLenZero_impliesSourceLenZero cellLower
        (rawCell_targetLenZero_impliesSourceLenZero cellUpper hlen)
  | _, _, _, _, .whiskerLeft whisker body, hlen =>
      Eq.trans (ModalityPath.length_composePath whisker _)
        (natSumZero (Nat.eq_zero_of_add_eq_zero_right (ModalityPath.length_composePath whisker _ ▸ hlen))
          (rawCell_targetLenZero_impliesSourceLenZero body
            (Nat.eq_zero_of_add_eq_zero_left (ModalityPath.length_composePath whisker _ ▸ hlen))))
  | _, _, _, _, .whiskerRight whisker body, hlen =>
      Eq.trans (ModalityPath.length_composePath _ whisker)
        (natSumZero
          (rawCell_targetLenZero_impliesSourceLenZero body
            (Nat.eq_zero_of_add_eq_zero_right (ModalityPath.length_composePath _ whisker ▸ hlen)))
          (Nat.eq_zero_of_add_eq_zero_left (ModalityPath.length_composePath _ whisker ▸ hlen)))

/-! ## The mu-iso composites (conv-free constructions) -/

/-- The composite `mu ∘ (eta ▷ t) : t.t ⇒ t ⇒ t.t` — multiply the two `t`'s, then re-grow one by the unit
whiskered on the right.  In an idempotent monad this is the identity `id_{t.t}` (the mu-iso "other composite"). -/
noncomputable def mulThenUnitRightWhisker :
    RawTwoCellExpr monadModeSignature monadTThenT (composePath monadT monadT) :=
  RawTwoCellExpr.vcomp monadMulTwoCell monadEtaTCell

/-- The Godement horizontal composite `eta ⊠ mu : t.t ⇒ t.t` — the `whiskerRight`-then-`whiskerLeft` order,
`(eta ▷ t.t) ∘ (t ◁ mu)`. -/
noncomputable def godementUnitMul :=
  RawTwoCellExpr.hcomp (signature := monadModeSignature) monadUnitTwoCell monadMulTwoCell

/-! ## The grow tower + the through-`t` canonical cell -/

/-- ★ The **grow tower** `t ⇒ t^{k+1}` — grow a single `t` up to `t^{k+1}` by inserting `k` units.  `k = 0` is the
identity `id_t : t ⇒ t^1`; the successor prepends one `eta ▷ t : t ⇒ t.t` and left-whiskers the shorter tower by
`t`.  Left-recursive to line up definitionally with `monadGadget`'s left-whisker fold. -/
def growTower : (k : Nat) → RawTwoCellExpr monadModeSignature monadT (monadTPower (k + 1))
  | 0 => RawTwoCellExpr.id (signature := monadModeSignature) monadT
  | k + 1 =>
      RawTwoCellExpr.vcomp monadEtaTCell
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower k))

/-- The **through-`t` canonical cell** `t^m ⇒ t^{targetPred+1}`: fold `t^m` down to a single `t` (`monadGadget m`)
then grow it back up to `t^{targetPred+1}` (`growTower targetPred`).  Total and cell-INDEPENDENT for every nonempty
target — the boundary-determined representative every populated hom collapses onto. -/
def canonThroughT (sourceCount targetPred : Nat) :
    RawTwoCellExpr monadModeSignature (monadTPower sourceCount) (monadTPower (targetPred + 1)) :=
  RawTwoCellExpr.vcomp (monadGadget sourceCount) (growTower targetPred)

/-- Smoke: `growTower 0` is the identity `id_t` (no insertion). -/
theorem growTower_zero :
    growTower 0 = RawTwoCellExpr.id (signature := monadModeSignature) monadT := rfl

/-- Smoke: `growTower 1 : t ⇒ t.t` unfolds to a genuine composite `eta ▷ t` then `t ◁ id_t`. -/
theorem growTower_one_unfold :
    growTower 1 = RawTwoCellExpr.vcomp monadEtaTCell
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (RawTwoCellExpr.id (signature := monadModeSignature) monadT)) := rfl

/-! ## `t`-power ordinal-sum boundary lemmas (`Nat` / `composePath`) -/

/-- `t^(inner+outer) = t^outer · t^inner` — the ordinal sum with the recursion summand `outer` on the LEFT of the
`composePath` (`monadTPower_add` after `add_comm`). -/
theorem monadTPower_add_left (outer inner : Nat) :
    monadTPower (inner + outer) = composePath (monadTPower outer) (monadTPower inner) := by
  rw [Nat.add_comm inner outer]; exact monadTPower_add outer inner

/-- `t^((inner+outer)+1) = t^outer · t^(inner+1)` — the successor form of `monadTPower_add_left` (through
`succ_add`). -/
theorem monadTPower_succ_add_left (outer inner : Nat) :
    monadTPower ((inner + outer) + 1) = composePath (monadTPower outer) (monadTPower (inner + 1)) := by
  rw [show (inner + outer) + 1 = (inner + 1) + outer from (Nat.succ_add inner outer).symm]
  exact monadTPower_add_left outer (inner + 1)

/-- `t^a · t = t^(a+1)` — the append-of-one boundary equality (`monadTPower_add a 1`, `monadTPower 1 = t` defeq). -/
theorem composePath_monadTPower_monadT (a : Nat) :
    composePath (monadTPower a) monadT = monadTPower (a + 1) :=
  (monadTPower_add a 1).symm

/-- Whiskering by PROPOSITIONALLY-equal 1-cells gives boundary-cast-equal cells: replacing the right-whisker
1-cell `oneCell` by an equal `oneCell'` transports the whiskered cell along the induced boundary equalities
(`cases` on the whisker equality). -/
theorem whiskerRight_whiskerEq {signature : ModeSignature} {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCell oneCell' : ModalityPath signature.graph middleMode targetMode} (hW : oneCell = oneCell')
    {oneCellDom oneCellCod : ModalityPath signature.graph sourceMode middleMode}
    (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
    RawTwoCellExpr.whiskerRight oneCell' body
      = RawTwoCellExpr.castBoundary (congrArg (composePath oneCellDom) hW)
          (congrArg (composePath oneCellCod) hW)
          (RawTwoCellExpr.whiskerRight oneCell body) := by
  cases hW; rfl

/-- `t^((inner+outer)+1) = t^(inner+1) · t^outer` — the RIGHT-append form of the successor ordinal sum (through
`succ_add`). -/
theorem monadTPower_succ_add_right (inner outer : Nat) :
    monadTPower ((inner + outer) + 1) = composePath (monadTPower (inner + 1)) (monadTPower outer) := by
  rw [show (inner + outer) + 1 = (inner + 1) + outer from (Nat.succ_add inner outer).symm]
  exact monadTPower_add (inner + 1) outer

/-! ## The normal-form boundary representative -/

/-- ★ The **normal-form boundary representative** — reads the two boundary lengths and returns the canonical cell
of the `t^sourceLen ⇒ t^targetLen` hom, in `monadTPower` coordinates.  Full-enum `Nat` match (propext-clean); the
empty hom `t^{sourceCount+1} ⇒ t^0` is refuted by cell-level rigidity. -/
def repNF : (sourceLen targetLen : Nat) →
    RawTwoCellExpr monadModeSignature (monadTPower sourceLen) (monadTPower targetLen) →
    RawTwoCellExpr monadModeSignature (monadTPower sourceLen) (monadTPower targetLen)
  | sourceLen, targetPred + 1, _ => canonThroughT sourceLen targetPred
  | 0, 0, _ => RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0)
  | sourceCount + 1, 0, cell =>
      Nat.noConfusion ((monadTPower_length (sourceCount + 1)).symm.trans
        (rawCell_targetLenZero_impliesSourceLenZero cell rfl))

/-- ★ **`repNF` is cell-INDEPENDENT** (boundary-determined): parallel cells get the same `repNF`.  Full-enum `Nat`
match, every branch `rfl`. -/
theorem repNF_cellIndependent : (sourceLen targetLen : Nat) →
    (cellA cellB : RawTwoCellExpr monadModeSignature (monadTPower sourceLen) (monadTPower targetLen)) →
    repNF sourceLen targetLen cellA = repNF sourceLen targetLen cellB
  | _, _ + 1, _, _ => rfl
  | 0, 0, _, _ => rfl
  | _ + 1, 0, _, _ => rfl

/-- ★ The **boundary-determined total representative**: transport `cell` to normal-form coordinates
(`monadPath_normalForm`), apply `repNF`, transport back.  Depends on `cell` only through `repNF`, so it is
BOUNDARY-DETERMINED. -/
def repFull {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    RawTwoCellExpr monadModeSignature sourcePath targetPath :=
  match sourceMode, targetMode with
  | MonadMode.point, MonadMode.point =>
      RawTwoCellExpr.castBoundary (monadPath_normalForm sourcePath).symm (monadPath_normalForm targetPath).symm
        (repNF sourcePath.length targetPath.length
          (RawTwoCellExpr.castBoundary (monadPath_normalForm sourcePath) (monadPath_normalForm targetPath) cell))

/-- ★ **`repFull` is boundary-determined**: parallel cells get equal `repFull`. -/
theorem repFull_boundary {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    repFull cellA = repFull cellB := by
  cases sourceMode; cases targetMode
  show RawTwoCellExpr.castBoundary _ _
      (repNF sourcePath.length targetPath.length (RawTwoCellExpr.castBoundary _ _ cellA))
    = RawTwoCellExpr.castBoundary _ _
      (repNF sourcePath.length targetPath.length (RawTwoCellExpr.castBoundary _ _ cellB))
  exact congrArg (RawTwoCellExpr.castBoundary _ _)
    (repNF_cellIndependent sourcePath.length targetPath.length _ _)

/-- Casting an identity across a boundary equality is the identity of the new boundary. -/
theorem castBoundary_id {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {onePath twoPath : ModalityPath signature.graph sourceMode targetMode} (hpath : onePath = twoPath) :
    RawTwoCellExpr.castBoundary hpath hpath (RawTwoCellExpr.id (signature := signature) onePath)
      = RawTwoCellExpr.id (signature := signature) twoPath := by
  cases hpath; rfl

/-- `repNF` on a populated target reduces to the through-`t` canonical cell, once the target length is exhibited as
a successor (`cases` on the length proof). -/
theorem repNF_of_targetLen {sourceLen targetLen : Nat}
    (cell : RawTwoCellExpr monadModeSignature (monadTPower sourceLen) (monadTPower targetLen))
    (targetPred : Nat) (htarget : targetLen = targetPred + 1) :
    repNF sourceLen targetLen cell
      = RawTwoCellExpr.castBoundary rfl (congrArg monadTPower htarget).symm (canonThroughT sourceLen targetPred) := by
  cases htarget; rfl

/-- `repFull` in point-to-point coordinates unfolds definitionally to its `monadPath_normalForm`-transported
`repNF` body.  Stated as an `rfl`. -/
theorem repFull_def {sourcePath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    repFull cell = RawTwoCellExpr.castBoundary (monadPath_normalForm sourcePath).symm
      (monadPath_normalForm targetPath).symm
      (repNF sourcePath.length targetPath.length
        (RawTwoCellExpr.castBoundary (monadPath_normalForm sourcePath) (monadPath_normalForm targetPath) cell)) :=
  rfl

/-- Transport `repNF` along `Nat` boundary-length equalities (`cases` both, then `rfl`). -/
theorem repNF_lengthCast {sourceLen sourceLen' targetLen targetLen' : Nat}
    (hsource : sourceLen = sourceLen') (htarget : targetLen = targetLen')
    (cell : RawTwoCellExpr monadModeSignature (monadTPower sourceLen) (monadTPower targetLen)) :
    repNF sourceLen targetLen cell
      = RawTwoCellExpr.castBoundary (congrArg monadTPower hsource).symm (congrArg monadTPower htarget).symm
        (repNF sourceLen' targetLen'
          (RawTwoCellExpr.castBoundary (congrArg monadTPower hsource) (congrArg monadTPower htarget) cell)) := by
  cases hsource; cases htarget; rfl

end FX1Poly.Polygraph
