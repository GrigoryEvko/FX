import FX1Poly.Typed.BoundExceedsPi
import FX1Poly.Typed.BoundExceedsDischarge

/-! # FX1Poly/Typed/BoundExceedsPiDischarge
    — the BFT-12b discharge core for the GROWN budget: monotonicity + existence

The grown analogue of `BoundExceedsDischarge.lean`.  Ships the two structural facts on `BoundExceedsPi` that the
grown fundamental-theorem discharge (BFT-12c) consumes to thread a SINGLE bound through `HasTypeDescPi`:

  * **`monotoneInBound`** — `BoundExceedsPi` is upward-monotone in the bound (+ telescope twin).  Term-mode `match`
    on the budget; the `conv` arm pins the implicit `Conv` proof in the pattern; the `ofFormation` arm lifts its
    carried `BoundExceeds` through the already-shipped `BoundExceeds.monotoneInBound`.
  * **`existsBound`** — every grown derivation HAS a budget (+ telescope twin).  Via `HasTypeDescPi.rec` (propext-
    free), SUM bounds combined through `Nat.le_add_right` / `Nat.le_add_left` (the `piIntro` arm sums THREE
    sub-bounds, chaining with `Nat.le_trans`).  The `ofFormation` arm DELEGATES to `BoundExceeds.existsBound` on the
    embedded formation derivation — this is where the per-term `belowBound` fuel originates.

Mirror of the formation discharge in every respect except the `ofFormation` delegation and the three-way `piIntro`
sum.  Together with BFT-12c (`BoundExceedsPi.rec` dispatch, `ofFormation` arm feeding `HasTypeDesc.fundamentalAt\
BoundedSucc`/BFT-11) and BFT-13 (closed corollary picking the bound via `existsBound`), this removes the last
quantitative hypothesis on the way to SN-043.

## Zero-axiom verification

`monotoneInBound` is a term-mode structural `match` on the budget; `existsBound` is a `HasTypeDescPi.rec` /
`DescTelescopePi.rec` application reusing `monotoneInBound`, `BoundExceeds.existsBound`, `Nat.le_add_right` /
`Nat.le_add_left` / `Nat.le_trans`.  No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega` (checked: depends on no axioms).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

mutual
/-- **The grown budget is monotone in the bound (term arm).**  Term-mode structural `match` on the budget; the
`conv` arm pins the implicit `converts`, the `ofFormation` arm lifts its carried `BoundExceeds` via the shipped
`BoundExceeds.monotoneInBound`.  Mutual with `BoundExceedsPiTelescope.monotoneInBound`. -/
theorem BoundExceedsPi.monotoneInBound {profile : PolyProfile} {env : Nat → Nat} {bound higherBound : Nat}
    (hle : bound ≤ higherBound) {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} {d : HasTypeDescPi profile context subject classifier}
    (budget : BoundExceedsPi env bound d) : BoundExceedsPi env higherBound d :=
  match budget with
  | .ofFormation formationBudget => .ofFormation (BoundExceeds.monotoneInBound hle formationBudget)
  | .conv (converts := convertsProof) levelExpr flag subjectBudget reclassifierBudget =>
      .conv (converts := convertsProof) levelExpr flag
        (BoundExceedsPi.monotoneInBound hle subjectBudget)
        (BoundExceedsPi.monotoneInBound hle reclassifierBudget)
  | .piIntro domainLevel codomainLevel flag domainBudget codomainBudget bodyBudget =>
      .piIntro domainLevel codomainLevel flag
        (BoundExceedsPi.monotoneInBound hle domainBudget)
        (BoundExceedsPi.monotoneInBound hle codomainBudget)
        (BoundExceedsPi.monotoneInBound hle bodyBudget)
  | .piElim functionBudget argumentBudget =>
      .piElim (BoundExceedsPi.monotoneInBound hle functionBudget)
        (BoundExceedsPi.monotoneInBound hle argumentBudget)
  | .genFormationPi context generator payload children levels flag rule isFormation premisesBudget =>
      .genFormationPi context generator payload children levels flag rule isFormation
        (BoundExceedsPiTelescope.monotoneInBound hle premisesBudget)
/-- **The grown telescope budget is monotone in the bound (telescope arm).**  Mutual companion; lifts each
head/rest sub-budget structurally. -/
theorem BoundExceedsPiTelescope.monotoneInBound {profile : PolyProfile} {env : Nat → Nat}
    {bound higherBound : Nat} (hle : bound ≤ higherBound) {baseScope currentDepth : Nat}
    {binderShifts : List Nat} {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag} {children : RawTermChildren binderShifts baseScope}
    {t : DescTelescopePi profile context levels flag children}
    (budget : BoundExceedsPiTelescope env bound t) : BoundExceedsPiTelescope env higherBound t :=
  match budget with
  | .nil context flag => .nil context flag
  | .cons context head headLevel restLevels flag rest headBudget restBudget =>
      .cons context head headLevel restLevels flag rest
        (BoundExceedsPi.monotoneInBound hle headBudget)
        (BoundExceedsPiTelescope.monotoneInBound hle restBudget)
end

/-- **Every grown derivation has a budget.**  `∃ bound, BoundExceedsPi env bound d` by `HasTypeDescPi.rec`: the
`ofFormation` arm delegates to `BoundExceeds.existsBound` on the embedded formation derivation (the origin of the
per-term fuel); recursive arms take the SUM of sub-bounds (the `piIntro` arm a three-way sum, chained with
`Nat.le_trans`) and lift each sub-budget through `monotoneInBound`.  Propext-free (the primitive recursor). -/
theorem BoundExceedsPi.existsBound {profile : PolyProfile} {env : Nat → Nat} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (d : HasTypeDescPi profile context subject classifier) : ∃ bound, BoundExceedsPi env bound d :=
  HasTypeDescPi.rec
    (motive_1 := fun {_scope} _context _subject _classifier d => ∃ bound, BoundExceedsPi env bound d)
    (motive_2 := fun {_baseScope _currentDepth _binderShifts} _context _levels _flag _children t =>
      ∃ bound, BoundExceedsPiTelescope env bound t)
    (fun formationTyped =>
      let ⟨formationBound, formationBudget⟩ := BoundExceeds.existsBound (env := env) formationTyped
      ⟨formationBound, BoundExceedsPi.ofFormation formationBudget⟩)
    (fun levelExpr flag _typed converts _reclassifierTyped subjectExists reclassifierExists =>
      let ⟨subjectBound, subjectBudget⟩ := subjectExists
      let ⟨reclassifierBound, reclassifierBudget⟩ := reclassifierExists
      ⟨subjectBound + reclassifierBound,
        BoundExceedsPi.conv (converts := converts) levelExpr flag
          (BoundExceedsPi.monotoneInBound (Nat.le_add_right subjectBound reclassifierBound) subjectBudget)
          (BoundExceedsPi.monotoneInBound (Nat.le_add_left reclassifierBound subjectBound) reclassifierBudget)⟩)
    (fun domainLevel codomainLevel flag _domainTyped _codomainTyped _bodyTyped
        domainExists codomainExists bodyExists =>
      let ⟨domainBound, domainBudget⟩ := domainExists
      let ⟨codomainBound, codomainBudget⟩ := codomainExists
      let ⟨bodyBound, bodyBudget⟩ := bodyExists
      ⟨domainBound + codomainBound + bodyBound,
        BoundExceedsPi.piIntro domainLevel codomainLevel flag
          (BoundExceedsPi.monotoneInBound
            (Nat.le_trans (Nat.le_add_right domainBound codomainBound)
              (Nat.le_add_right (domainBound + codomainBound) bodyBound)) domainBudget)
          (BoundExceedsPi.monotoneInBound
            (Nat.le_trans (Nat.le_add_left codomainBound domainBound)
              (Nat.le_add_right (domainBound + codomainBound) bodyBound)) codomainBudget)
          (BoundExceedsPi.monotoneInBound
            (Nat.le_add_left bodyBound (domainBound + codomainBound)) bodyBudget)⟩)
    (fun _functionTyped _argumentTyped functionExists argumentExists =>
      let ⟨functionBound, functionBudget⟩ := functionExists
      let ⟨argumentBound, argumentBudget⟩ := argumentExists
      ⟨functionBound + argumentBound,
        BoundExceedsPi.piElim
          (BoundExceedsPi.monotoneInBound (Nat.le_add_right functionBound argumentBound) functionBudget)
          (BoundExceedsPi.monotoneInBound (Nat.le_add_left argumentBound functionBound) argumentBudget)⟩)
    (fun context generator payload children levels flag rule isFormation _premises premisesExists =>
      let ⟨premisesBound, premisesBudget⟩ := premisesExists
      ⟨premisesBound,
        BoundExceedsPi.genFormationPi context generator payload children levels flag rule isFormation
          premisesBudget⟩)
    (fun context flag => ⟨0, BoundExceedsPiTelescope.nil context flag⟩)
    (fun context head headLevel restLevels flag rest _headTyped _restTyped headExists restExists =>
      let ⟨headBound, headBudget⟩ := headExists
      let ⟨restBound, restBudget⟩ := restExists
      ⟨headBound + restBound,
        BoundExceedsPiTelescope.cons context head headLevel restLevels flag rest
          (BoundExceedsPi.monotoneInBound (Nat.le_add_right headBound restBound) headBudget)
          (BoundExceedsPiTelescope.monotoneInBound (Nat.le_add_left restBound headBound) restBudget)⟩)
    d

/-- **Every grown telescope has a budget.**  The `DescTelescopePi.rec` twin of `BoundExceedsPi.existsBound` (same
arm set, returns the telescope motive); supplies the bound that the genFormationPi arm of BFT-12c reads off its
premises telescope. -/
theorem BoundExceedsPiTelescope.existsBound {profile : PolyProfile} {env : Nat → Nat}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)} {levels : List LevelExpr}
    {flag : UniverseFlag} {children : RawTermChildren binderShifts baseScope}
    (t : DescTelescopePi profile context levels flag children) :
    ∃ bound, BoundExceedsPiTelescope env bound t :=
  DescTelescopePi.rec
    (motive_1 := fun {_scope} _context _subject _classifier d => ∃ bound, BoundExceedsPi env bound d)
    (motive_2 := fun {_baseScope _currentDepth _binderShifts} _context _levels _flag _children t =>
      ∃ bound, BoundExceedsPiTelescope env bound t)
    (fun formationTyped =>
      let ⟨formationBound, formationBudget⟩ := BoundExceeds.existsBound (env := env) formationTyped
      ⟨formationBound, BoundExceedsPi.ofFormation formationBudget⟩)
    (fun levelExpr flag _typed converts _reclassifierTyped subjectExists reclassifierExists =>
      let ⟨subjectBound, subjectBudget⟩ := subjectExists
      let ⟨reclassifierBound, reclassifierBudget⟩ := reclassifierExists
      ⟨subjectBound + reclassifierBound,
        BoundExceedsPi.conv (converts := converts) levelExpr flag
          (BoundExceedsPi.monotoneInBound (Nat.le_add_right subjectBound reclassifierBound) subjectBudget)
          (BoundExceedsPi.monotoneInBound (Nat.le_add_left reclassifierBound subjectBound) reclassifierBudget)⟩)
    (fun domainLevel codomainLevel flag _domainTyped _codomainTyped _bodyTyped
        domainExists codomainExists bodyExists =>
      let ⟨domainBound, domainBudget⟩ := domainExists
      let ⟨codomainBound, codomainBudget⟩ := codomainExists
      let ⟨bodyBound, bodyBudget⟩ := bodyExists
      ⟨domainBound + codomainBound + bodyBound,
        BoundExceedsPi.piIntro domainLevel codomainLevel flag
          (BoundExceedsPi.monotoneInBound
            (Nat.le_trans (Nat.le_add_right domainBound codomainBound)
              (Nat.le_add_right (domainBound + codomainBound) bodyBound)) domainBudget)
          (BoundExceedsPi.monotoneInBound
            (Nat.le_trans (Nat.le_add_left codomainBound domainBound)
              (Nat.le_add_right (domainBound + codomainBound) bodyBound)) codomainBudget)
          (BoundExceedsPi.monotoneInBound
            (Nat.le_add_left bodyBound (domainBound + codomainBound)) bodyBudget)⟩)
    (fun _functionTyped _argumentTyped functionExists argumentExists =>
      let ⟨functionBound, functionBudget⟩ := functionExists
      let ⟨argumentBound, argumentBudget⟩ := argumentExists
      ⟨functionBound + argumentBound,
        BoundExceedsPi.piElim
          (BoundExceedsPi.monotoneInBound (Nat.le_add_right functionBound argumentBound) functionBudget)
          (BoundExceedsPi.monotoneInBound (Nat.le_add_left argumentBound functionBound) argumentBudget)⟩)
    (fun context generator payload children levels flag rule isFormation _premises premisesExists =>
      let ⟨premisesBound, premisesBudget⟩ := premisesExists
      ⟨premisesBound,
        BoundExceedsPi.genFormationPi context generator payload children levels flag rule isFormation
          premisesBudget⟩)
    (fun context flag => ⟨0, BoundExceedsPiTelescope.nil context flag⟩)
    (fun context head headLevel restLevels flag rest _headTyped _restTyped headExists restExists =>
      let ⟨headBound, headBudget⟩ := headExists
      let ⟨restBound, restBudget⟩ := restExists
      ⟨headBound + restBound,
        BoundExceedsPiTelescope.cons context head headLevel restLevels flag rest
          (BoundExceedsPi.monotoneInBound (Nat.le_add_right headBound restBound) headBudget)
          (BoundExceedsPiTelescope.monotoneInBound (Nat.le_add_left restBound headBound) restBudget)⟩)
    t

end FX1Poly.Typed
