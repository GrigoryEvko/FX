import FX1Poly.Tier0.Mode.FreeTwoCellModel

/-! # mode-3 floor — decidable SYNTACTIC equality of free 2-cell expressions

`FreeTwoCellModel` deferred decidable syntactic equality of `RawTwoCellExpr` (the free 2-cell terms): the
whisker constructors are indexed by `composePath`-applications, and `composePath f g` does not determine the
split `(f, g)`, so the dependent matcher cannot take two whisker-headed cells apart jointly (it would have to
unify two `composePath`s).  That is exactly why `FreeTwoCellModel` listed decidable equality as blocked.

This file DECIDES it — a propext-clean `DecidableEq (RawTwoCellExpr signature sourcePath targetPath)` given
decidable equality on modes, modality generators, and 2-cell generators.  The indexed-`DecidableEq`-propext
trap (a `deriving`/joint match on the indexed inductive leaks `propext`) is dodged by recursion on the LEFT
cell only, never matching the RIGHT cell directly: each constructor of `right` is exposed by a single-recursion
VIEW function (`asGen` / `asVcomp` / `asWhiskerLeft` / `asWhiskerRight`, each carrying a reconstruction
certificate) plus the `isIdentityCell` probe for the identity head.  The whisker-split wrinkle is mechanical:

  * `composePathLeftCancel` / `composePathRightCancel` — the free 1-cell monoid is two-sided cancellative
    (the right-cancellation goes through a length argument, `rightFactorNeConsExtension`).  Once the whisker
    1-cells are decided equal, cancellation recovers the body boundary paths, so the recursive body comparison
    typechecks.
  * the per-head packed extractors (`genPacked`, `vcompMiddlePacked`, `whiskerLeftPackedOneCell`,
    `whiskerRightPackedOneCell`) drive the NEGATIVE directions cast-free (`congrArg` a function whose codomain
    does not mention the cell, then `Option.some.inj` / `PSigma.mk.inj`).
  * the reconstruction certificates drive the POSITIVE directions: after substituting the decided component
    equalities, the `composePath`-factor proofs collapse to `rfl` by proof irrelevance, so the cast in the
    whisker views vanishes and `right` is literally the matched head of `left`.

`RawTwoCellExpr.decEq` recurses structurally on the left cell; with this in hand the convergent normalizer's
`interchangeFreeConv_iff_normalFormEq` becomes a literal `Decidable` (the interchange-free decision file).

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free
(structural recursion + `injection` + `eq_of_heq` on equal-index heads; the manual `natAddRightCancel` avoids
core's `propext`-routed `Nat.add_right_cancel`).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Tier0

/-! ## Path-composition cancellation -/

theorem composePathLeftCancel {graph : ModeGraph} {modeA modeB modeC : graph.Mode}
    (leftFactor : ModalityPath graph modeA modeB) :
    {firstRight secondRight : ModalityPath graph modeB modeC} →
    composePath leftFactor firstRight = composePath leftFactor secondRight → firstRight = secondRight := by
  induction leftFactor with
  | nil _ => intro firstRight secondRight composedEqual; exact composedEqual
  | cons _ _ inductionHypothesis =>
      intro firstRight secondRight composedEqual
      injection composedEqual with _e1 _e2 _e3 _e4 tailEqual
      exact inductionHypothesis tailEqual

theorem natAddRightCancel {leftSummand rightSummand : Nat} :
    {cancelled : Nat} → leftSummand + cancelled = rightSummand + cancelled → leftSummand = rightSummand := by
  intro cancelled
  induction cancelled with
  | zero => intro equalSums; exact equalSums
  | succ _ inductionHypothesis => intro equalSums; exact inductionHypothesis (Nat.succ.inj equalSums)

theorem lengthComposePath {graph : ModeGraph} {modeA modeB modeC : graph.Mode}
    (first : ModalityPath graph modeA modeB) (second : ModalityPath graph modeB modeC) :
    (composePath first second).length = first.length + second.length := by
  induction first with
  | nil _ => exact (Nat.zero_add second.length).symm
  | cons _ rest inductionHypothesis =>
      dsimp only [composePath, ModalityPath.length]
      rw [inductionHypothesis, Nat.succ_add]

theorem rightFactorNeConsExtension {graph : ModeGraph} {modeB modeC modeMid : graph.Mode}
    (rightFactor : ModalityPath graph modeB modeC)
    (modality : graph.Modality modeB modeMid) (rest : ModalityPath graph modeMid modeB) :
    rightFactor = ModalityPath.cons modality (composePath rest rightFactor) → False := by
  intro selfExtends
  have lengthsEqual : rightFactor.length = (rest.length + rightFactor.length) + 1 :=
    (congrArg ModalityPath.length selfExtends).trans (by
      dsimp only [ModalityPath.length]; rw [lengthComposePath])
  have rearranged : (rest.length + 1) + rightFactor.length = 0 + rightFactor.length := by
    rw [Nat.zero_add, ← Nat.add_right_comm rest.length rightFactor.length 1, ← lengthsEqual]
  exact Nat.noConfusion (natAddRightCancel rearranged)

theorem composePathRightCancel {graph : ModeGraph} {modeB modeC : graph.Mode}
    (rightFactor : ModalityPath graph modeB modeC) :
    {modeA : graph.Mode} → (first second : ModalityPath graph modeA modeB) →
    composePath first rightFactor = composePath second rightFactor → first = second
  | _, .nil _, .nil _, _ => rfl
  | _, .nil _, .cons modalityTwo restTwo, factorsEqual =>
      absurd factorsEqual (rightFactorNeConsExtension rightFactor modalityTwo restTwo)
  | _, .cons modalityOne restOne, .nil _, factorsEqual =>
      absurd factorsEqual.symm (rightFactorNeConsExtension rightFactor modalityOne restOne)
  | _, .cons modalityOne restOne, .cons modalityTwo restTwo, factorsEqual => by
      injection factorsEqual with _sourceEqual middleEqual _targetEqual modalityHeq restFactorsHeq
      subst middleEqual
      have modalityEqual : modalityOne = modalityTwo := eq_of_heq modalityHeq
      have restEqual : restOne = restTwo :=
        composePathRightCancel rightFactor restOne restTwo (eq_of_heq restFactorsHeq)
      rw [modalityEqual, restEqual]

/-! ## The identity-head extraction -/

theorem RawTwoCellExpr.eq_id_of_isIdentityCell {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) (isId : cell.isIdentityCell = true) :
    ∃ (sourceEqTarget : sourcePath = targetPath), cell = sourceEqTarget ▸ RawTwoCellExpr.id sourcePath := by
  match cell with
  | .id _ => exact ⟨rfl, rfl⟩
  | .gen _ => exact nomatch isId
  | .vcomp _ _ => exact nomatch isId
  | .whiskerLeft _ _ => exact nomatch isId
  | .whiskerRight _ _ => exact nomatch isId

/-! ## Packed head extractors (cast-free, for the negative directions) -/

def RawTwoCellExpr.genPacked {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    Option (signature.twoCell sourcePath targetPath) :=
  match cell with
  | .gen generator => some generator
  | .id _ => none
  | .vcomp _ _ => none
  | .whiskerLeft _ _ => none
  | .whiskerRight _ _ => none

def RawTwoCellExpr.vcompMiddlePacked {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    Option (ModalityPath signature.graph sourceMode targetMode) :=
  match cell with
  | @RawTwoCellExpr.vcomp _ _ _ _ middle _ _ _ => some middle
  | .gen _ => none
  | .id _ => none
  | .whiskerLeft _ _ => none
  | .whiskerRight _ _ => none

def RawTwoCellExpr.whiskerLeftPackedOneCell {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    Option (PSigma (fun (middleMode : signature.graph.Mode) =>
      ModalityPath signature.graph sourceMode middleMode)) :=
  match cell with
  | @RawTwoCellExpr.whiskerLeft _ _ middleMode _ oneCell _ _ _ => some ⟨middleMode, oneCell⟩
  | .gen _ => none
  | .id _ => none
  | .vcomp _ _ => none
  | .whiskerRight _ _ => none

def RawTwoCellExpr.whiskerRightPackedOneCell {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    Option (PSigma (fun (middleMode : signature.graph.Mode) =>
      ModalityPath signature.graph middleMode targetMode)) :=
  match cell with
  | @RawTwoCellExpr.whiskerRight _ _ middleMode _ _ _ oneCell _ => some ⟨middleMode, oneCell⟩
  | .gen _ => none
  | .id _ => none
  | .vcomp _ _ => none
  | .whiskerLeft _ _ => none

/-! ## The head views (single-recursion on the cell, with reconstruction) -/

structure GenView {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) where
  generator : signature.twoCell sourcePath targetPath
  reconstruct : cell = RawTwoCellExpr.gen generator

structure VcompView {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) where
  middlePath : ModalityPath signature.graph sourceMode targetMode
  alpha : RawTwoCellExpr signature sourcePath middlePath
  beta : RawTwoCellExpr signature middlePath targetPath
  reconstruct : cell = RawTwoCellExpr.vcomp alpha beta

structure WhiskerLeftView {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) where
  middleMode : signature.graph.Mode
  oneCell : ModalityPath signature.graph sourceMode middleMode
  bodyDom : ModalityPath signature.graph middleMode targetMode
  bodyCod : ModalityPath signature.graph middleMode targetMode
  body : RawTwoCellExpr signature bodyDom bodyCod
  sourceFactors : sourcePath = composePath oneCell bodyDom
  targetFactors : targetPath = composePath oneCell bodyCod
  reconstruct : cell = sourceFactors ▸ targetFactors ▸ RawTwoCellExpr.whiskerLeft oneCell body
  packedOneCell : cell.whiskerLeftPackedOneCell = some ⟨middleMode, oneCell⟩

structure WhiskerRightView {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) where
  middleMode : signature.graph.Mode
  oneCell : ModalityPath signature.graph middleMode targetMode
  bodyDom : ModalityPath signature.graph sourceMode middleMode
  bodyCod : ModalityPath signature.graph sourceMode middleMode
  body : RawTwoCellExpr signature bodyDom bodyCod
  sourceFactors : sourcePath = composePath bodyDom oneCell
  targetFactors : targetPath = composePath bodyCod oneCell
  reconstruct : cell = sourceFactors ▸ targetFactors ▸ RawTwoCellExpr.whiskerRight oneCell body
  packedOneCell : cell.whiskerRightPackedOneCell = some ⟨middleMode, oneCell⟩

def RawTwoCellExpr.asGen {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) : Option (GenView cell) :=
  match cell with
  | .gen generator => some ⟨generator, rfl⟩
  | .id _ => none
  | .vcomp _ _ => none
  | .whiskerLeft _ _ => none
  | .whiskerRight _ _ => none

def RawTwoCellExpr.asVcomp {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) : Option (VcompView cell) :=
  match cell with
  | @RawTwoCellExpr.vcomp _ _ _ _ middle _ alpha beta => some ⟨middle, alpha, beta, rfl⟩
  | .gen _ => none
  | .id _ => none
  | .whiskerLeft _ _ => none
  | .whiskerRight _ _ => none

def RawTwoCellExpr.asWhiskerLeft {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) : Option (WhiskerLeftView cell) :=
  match cell with
  | @RawTwoCellExpr.whiskerLeft _ _ middleMode _ oneCell bodyDom bodyCod body =>
      some ⟨middleMode, oneCell, bodyDom, bodyCod, body, rfl, rfl, rfl, rfl⟩
  | .gen _ => none
  | .id _ => none
  | .vcomp _ _ => none
  | .whiskerRight _ _ => none

def RawTwoCellExpr.asWhiskerRight {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) : Option (WhiskerRightView cell) :=
  match cell with
  | @RawTwoCellExpr.whiskerRight _ _ middleMode _ bodyDom bodyCod oneCell body =>
      some ⟨middleMode, oneCell, bodyDom, bodyCod, body, rfl, rfl, rfl, rfl⟩
  | .gen _ => none
  | .id _ => none
  | .vcomp _ _ => none
  | .whiskerLeft _ _ => none

/-! ## Decidable equality -/

def RawTwoCellExpr.decEq {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath)) :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    (left right : RawTwoCellExpr signature sourcePath targetPath) → Decidable (left = right)
  | _, _, _, _, .gen leftGen, right =>
      match hView : right.asGen with
      | none =>
          isFalse (fun cellsEqual => by
            have hcontra : (RawTwoCellExpr.gen leftGen).asGen = none := by rw [cellsEqual]; exact hView
            dsimp only [RawTwoCellExpr.asGen] at hcontra
            exact nomatch hcontra)
      | some view => by
          obtain ⟨rightGen, reconstruct⟩ := view
          exact
            match twoCellDecEq _ _ leftGen rightGen with
            | isTrue genEqual => isTrue (by subst genEqual; exact reconstruct.symm)
            | isFalse genDiffer =>
                isFalse (fun cellsEqual => genDiffer (by
                  have hpacked : (RawTwoCellExpr.gen leftGen).genPacked = some rightGen :=
                    cellsEqual ▸ congrArg RawTwoCellExpr.genPacked reconstruct
                  exact Option.some.inj hpacked))
  | _, _, _, _, .id _, right =>
      match hId : right.isIdentityCell with
      | true =>
          isTrue (by
            obtain ⟨_sourceEqTarget, reconstruct⟩ := right.eq_id_of_isIdentityCell hId
            exact reconstruct.symm)
      | false =>
          isFalse (fun cellsEqual => by
            rw [← cellsEqual] at hId
            exact Bool.noConfusion hId)
  | _, _, _, _, @RawTwoCellExpr.vcomp _ _ _ _ leftMiddle _ leftAlpha leftBeta, right =>
      match hView : right.asVcomp with
      | none =>
          isFalse (fun cellsEqual => by
            have hcontra : (RawTwoCellExpr.vcomp leftAlpha leftBeta).asVcomp = none := by
              rw [cellsEqual]; exact hView
            dsimp only [RawTwoCellExpr.asVcomp] at hcontra
            exact nomatch hcontra)
      | some view => by
          obtain ⟨rightMiddle, rightAlpha, rightBeta, reconstruct⟩ := view
          exact
            match modalityPathDecEq modeDecEq modalityDecEq leftMiddle rightMiddle with
            | isFalse middlesDiffer =>
                isFalse (fun cellsEqual => middlesDiffer (by
                  have hpacked : (RawTwoCellExpr.vcomp leftAlpha leftBeta).vcompMiddlePacked
                      = some rightMiddle := cellsEqual ▸ congrArg RawTwoCellExpr.vcompMiddlePacked reconstruct
                  exact Option.some.inj hpacked))
            | isTrue middlesEqual => by
                subst middlesEqual
                exact
                  match RawTwoCellExpr.decEq modeDecEq modalityDecEq twoCellDecEq leftAlpha rightAlpha,
                        RawTwoCellExpr.decEq modeDecEq modalityDecEq twoCellDecEq leftBeta rightBeta with
                  | isTrue alphaEqual, isTrue betaEqual =>
                      isTrue (by subst alphaEqual; subst betaEqual; exact reconstruct.symm)
                  | isFalse alphaDiffer, _ =>
                      isFalse (fun cellsEqual => by
                        rw [reconstruct] at cellsEqual
                        injection cellsEqual with _e1 _e2 _e3 _e4 _e5 alphaEqual _betaEqual
                        exact alphaDiffer alphaEqual)
                  | _, isFalse betaDiffer =>
                      isFalse (fun cellsEqual => by
                        rw [reconstruct] at cellsEqual
                        injection cellsEqual with _e1 _e2 _e3 _e4 _e5 _alphaEqual betaEqual
                        exact betaDiffer betaEqual)
  | _, _, _, _, @RawTwoCellExpr.whiskerLeft _ _ leftMid _ leftOne leftDom leftCod leftBody, right =>
      match hView : right.asWhiskerLeft with
      | none =>
          isFalse (fun cellsEqual => by
            have hcontra : (RawTwoCellExpr.whiskerLeft leftOne leftBody).asWhiskerLeft = none := by
              rw [cellsEqual]; exact hView
            dsimp only [RawTwoCellExpr.asWhiskerLeft] at hcontra
            exact nomatch hcontra)
      | some view => by
          obtain ⟨rightMid, rightOne, rightDom, rightCod, rightBody, srcFactors, tgtFactors,
            reconstruct, packed⟩ := view
          exact
            match modeDecEq leftMid rightMid with
            | isFalse midsDiffer =>
                isFalse (fun cellsEqual => midsDiffer (by
                  have hpacked : (RawTwoCellExpr.whiskerLeft leftOne leftBody).whiskerLeftPackedOneCell
                      = some ⟨rightMid, rightOne⟩ := cellsEqual ▸ packed
                  exact congrArg PSigma.fst (Option.some.inj hpacked)))
            | isTrue midsEqual => by
                subst midsEqual
                exact
                  match modalityPathDecEq modeDecEq modalityDecEq leftOne rightOne with
                  | isFalse onesDiffer =>
                      isFalse (fun cellsEqual => onesDiffer (by
                        have hpacked : (RawTwoCellExpr.whiskerLeft leftOne leftBody).whiskerLeftPackedOneCell
                            = some ⟨leftMid, rightOne⟩ := cellsEqual ▸ packed
                        exact eq_of_heq (PSigma.mk.inj (Option.some.inj hpacked)).2))
                  | isTrue onesEqual => by
                      subst onesEqual
                      have domsEqual : leftDom = rightDom := composePathLeftCancel leftOne srcFactors
                      subst domsEqual
                      have codsEqual : leftCod = rightCod := composePathLeftCancel leftOne tgtFactors
                      subst codsEqual
                      have reconClean : right = RawTwoCellExpr.whiskerLeft leftOne rightBody := reconstruct
                      exact
                        match RawTwoCellExpr.decEq modeDecEq modalityDecEq twoCellDecEq leftBody rightBody with
                        | isTrue bodyEqual => isTrue (by subst bodyEqual; exact reconClean.symm)
                        | isFalse bodyDiffer =>
                            isFalse (fun cellsEqual => by
                              rw [reconClean] at cellsEqual
                              injection cellsEqual with _e1 _e2 _e3 _e4 _e5 _e6 bodyEqual
                              exact bodyDiffer bodyEqual)
  | _, _, _, _, @RawTwoCellExpr.whiskerRight _ _ leftMid _ leftDom leftCod leftOne leftBody, right =>
      match hView : right.asWhiskerRight with
      | none =>
          isFalse (fun cellsEqual => by
            have hcontra : (RawTwoCellExpr.whiskerRight leftOne leftBody).asWhiskerRight = none := by
              rw [cellsEqual]; exact hView
            dsimp only [RawTwoCellExpr.asWhiskerRight] at hcontra
            exact nomatch hcontra)
      | some view => by
          obtain ⟨rightMid, rightOne, rightDom, rightCod, rightBody, srcFactors, tgtFactors,
            reconstruct, packed⟩ := view
          exact
            match modeDecEq leftMid rightMid with
            | isFalse midsDiffer =>
                isFalse (fun cellsEqual => midsDiffer (by
                  have hpacked : (RawTwoCellExpr.whiskerRight leftOne leftBody).whiskerRightPackedOneCell
                      = some ⟨rightMid, rightOne⟩ := cellsEqual ▸ packed
                  exact congrArg PSigma.fst (Option.some.inj hpacked)))
            | isTrue midsEqual => by
                subst midsEqual
                exact
                  match modalityPathDecEq modeDecEq modalityDecEq leftOne rightOne with
                  | isFalse onesDiffer =>
                      isFalse (fun cellsEqual => onesDiffer (by
                        have hpacked : (RawTwoCellExpr.whiskerRight leftOne leftBody).whiskerRightPackedOneCell
                            = some ⟨leftMid, rightOne⟩ := cellsEqual ▸ packed
                        exact eq_of_heq (PSigma.mk.inj (Option.some.inj hpacked)).2))
                  | isTrue onesEqual => by
                      subst onesEqual
                      have domsEqual : leftDom = rightDom := composePathRightCancel leftOne leftDom rightDom srcFactors
                      subst domsEqual
                      have codsEqual : leftCod = rightCod := composePathRightCancel leftOne leftCod rightCod tgtFactors
                      subst codsEqual
                      have reconClean : right = RawTwoCellExpr.whiskerRight leftOne rightBody := reconstruct
                      exact
                        match RawTwoCellExpr.decEq modeDecEq modalityDecEq twoCellDecEq leftBody rightBody with
                        | isTrue bodyEqual => isTrue (by subst bodyEqual; exact reconClean.symm)
                        | isFalse bodyDiffer =>
                            isFalse (fun cellsEqual => by
                              rw [reconClean] at cellsEqual
                              injection cellsEqual with _e1 _e2 _e3 _e4 _e5 _e6 bodyEqual
                              exact bodyDiffer bodyEqual)

/-- ★ **Decidable equality of free 2-cell expressions** as a `DecidableEq` instance, given decidable
equality on the signature's modes, modality generators, and 2-cell generators. -/
def RawTwoCellExpr.decidableEq {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} :
    DecidableEq (RawTwoCellExpr signature sourcePath targetPath) :=
  fun left right => RawTwoCellExpr.decEq modeDecEq modalityDecEq twoCellDecEq left right

end FX1Poly.Tier0
