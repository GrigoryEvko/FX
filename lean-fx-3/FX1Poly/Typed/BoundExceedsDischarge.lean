import FX1Poly.Typed.BoundExceedsDesc

/-! # FX1Poly/Typed/BoundExceedsDischarge
    — the BFT-12 discharge core: monotonicity + existence of the per-derivation universe-level budget

`BoundExceedsDesc.lean` defines the indexed-inductive budget `BoundExceeds env bound d` (and its telescope
companion) asserting `bound` exceeds the denoted `lsucc`-level of every `universeFormation` leaf in the formation
derivation `d`.  The bounded grown fundamental theorem (BFT-11/`HasTypeDesc.fundamentalAtBoundedSucc`) will consume
the budget per-arm; to feed it a single concrete bound, this file ships the two structural facts:

  * **`monotoneInBound`** — the budget is upward-monotone in the bound (`bound ≤ bound' → BoundExceeds env bound d →
    BoundExceeds env bound' d`), needed to lift sub-derivation budgets to a common bound when combining.
  * **`existsBound`** — every formation derivation HAS a bound (`∃ bound, BoundExceeds env bound d`), constructed by
    structural recursion: `var` needs none (`0`), `universeFormation` supplies `denote (lsucc levelExpr) env + 1`,
    and the recursive arms (`conv`, `genFormation`, telescope `cons`) take the SUM of the sub-bounds and lift each
    sub-budget through `monotoneInBound`.

Together: `existsBound` produces the `bound` that BFT-12 threads through the bounded grown FT (BFT-6 dispatch),
discharging the per-term "fuel" the bounded route needs and removing the last quantitative hypothesis on the way
to SN-043.

## The combined bound is a SUM, not a `max`

The natural choice would be `max`, but `Nat.le_max_left` / `Nat.le_max_right` in Init are proved via the `if`-form
of `Nat.max` and DEPEND ON `propext`.  Addition gives the same "exceeds both" guarantee through the propext-free
`Nat.le_add_right` / `Nat.le_add_left`, so the combined bound is `subjectBound + reclassifierBound` (and
`headBound + restBound` for the telescope) — keeping the discharge zero-axiom.

## Why `existsBound` routes through the recursor, not `match`

`monotoneInBound` matches on the BUDGET (a freshly-defined inductive whose generated `casesOn` is clean), so its
term-mode `match` stays propext-free.  `existsBound` must case-split on the FORMATION derivation `d : HasTypeDesc`
with a dependent motive `∃ bound, BoundExceeds env bound d`; a term-mode `match` on that indexed family compiles to
a custom splitter that drags in `propext` (index `noConfusion`).  The primitive recursor `HasTypeDesc.rec` /
`DescTelescope.rec` is propext-free by construction, so `existsBound` is written directly against it.

## Zero-axiom verification

`monotoneInBound` is a term-mode structural `match` on the budget (the `conv` arm pins the `Conv` proof by binding
the implicit `converts` in the pattern).  `existsBound` is a `HasTypeDesc.rec` / `DescTelescope.rec` application
whose arms reuse `monotoneInBound`, `Nat.le_add_right`, `Nat.le_add_left`, `Nat.lt_succ_self`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (checked: depends on no axioms).  Per-declaration
gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

mutual
/-- **The budget is monotone in the bound (term arm).**  A bound that exceeds every `universeFormation` level in
`d` is still exceeded by any larger bound.  Term-mode structural `match` on the budget; the `conv` arm binds the
implicit `converts` proof in the pattern so the reconstructed `BoundExceeds.conv` reuses the exact same conversion.
Mutual with `BoundExceedsTelescope.monotoneInBound`. -/
theorem BoundExceeds.monotoneInBound {profile : PolyProfile} {env : Nat → Nat} {bound higherBound : Nat}
    (hle : bound ≤ higherBound) {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} {d : HasTypeDesc profile context subject classifier}
    (budget : BoundExceeds env bound d) : BoundExceeds env higherBound d :=
  match budget with
  | .var context index => .var context index
  | .conv (converts := convertsProof) levelExpr flag subjectBudget reclassifierBudget =>
      .conv (converts := convertsProof) levelExpr flag
        (BoundExceeds.monotoneInBound hle subjectBudget)
        (BoundExceeds.monotoneInBound hle reclassifierBudget)
  | .universeFormation context levelExpr flag belowBound =>
      .universeFormation context levelExpr flag (Nat.lt_of_lt_of_le belowBound hle)
  | .genFormation context generator payload children levels flag rule isFormation premisesBudget =>
      .genFormation context generator payload children levels flag rule isFormation
        (BoundExceedsTelescope.monotoneInBound hle premisesBudget)
/-- **The telescope budget is monotone in the bound (telescope arm).**  Mutual companion of
`BoundExceeds.monotoneInBound`; lifts each head/rest sub-budget structurally. -/
theorem BoundExceedsTelescope.monotoneInBound {profile : PolyProfile} {env : Nat → Nat}
    {bound higherBound : Nat} (hle : bound ≤ higherBound) {baseScope currentDepth : Nat}
    {binderShifts : List Nat} {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag} {children : RawTermChildren binderShifts baseScope}
    {t : DescTelescope profile context levels flag children}
    (budget : BoundExceedsTelescope env bound t) : BoundExceedsTelescope env higherBound t :=
  match budget with
  | .nil context flag => .nil context flag
  | .cons context head headLevel restLevels flag rest headBudget restBudget =>
      .cons context head headLevel restLevels flag rest
        (BoundExceeds.monotoneInBound hle headBudget)
        (BoundExceedsTelescope.monotoneInBound hle restBudget)
end

/-- **Every formation derivation has a budget.**  `∃ bound, BoundExceeds env bound d` by structural recursion on
the formation derivation `d`: the `var` leaf needs no fuel (`0`); the `universeFormation` leaf supplies
`denote (lsucc levelExpr) env + 1` (so `Nat.lt_succ_self` discharges its `belowBound`); recursive arms take the SUM
of the sub-bounds and lift each sub-budget through `monotoneInBound` (sum, not `max`, because the Init `max`
le-lemmas leak `propext`).  Written against `HasTypeDesc.rec` (propext-free) rather than a `match` on the indexed
family. -/
theorem BoundExceeds.existsBound {profile : PolyProfile} {env : Nat → Nat} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (d : HasTypeDesc profile context subject classifier) : ∃ bound, BoundExceeds env bound d :=
  HasTypeDesc.rec
    (motive_1 := fun {_scope} _context _subject _classifier d => ∃ bound, BoundExceeds env bound d)
    (motive_2 := fun {_baseScope _currentDepth _binderShifts} _context _levels _flag _children t =>
      ∃ bound, BoundExceedsTelescope env bound t)
    (fun context index => ⟨0, BoundExceeds.var context index⟩)
    (fun levelExpr flag _typed converts _reclassifierTyped subjectExists reclassifierExists =>
      let ⟨subjectBound, subjectBudget⟩ := subjectExists
      let ⟨reclassifierBound, reclassifierBudget⟩ := reclassifierExists
      ⟨subjectBound + reclassifierBound,
        BoundExceeds.conv (converts := converts) levelExpr flag
          (BoundExceeds.monotoneInBound (Nat.le_add_right subjectBound reclassifierBound) subjectBudget)
          (BoundExceeds.monotoneInBound (Nat.le_add_left reclassifierBound subjectBound) reclassifierBudget)⟩)
    (fun context levelExpr flag =>
      ⟨LevelExpr.denote (LevelExpr.lsucc levelExpr) env + 1,
        BoundExceeds.universeFormation context levelExpr flag (Nat.lt_succ_self _)⟩)
    (fun context generator payload children levels flag rule isFormation _premises premisesExists =>
      let ⟨premisesBound, premisesBudget⟩ := premisesExists
      ⟨premisesBound,
        BoundExceeds.genFormation context generator payload children levels flag rule isFormation
          premisesBudget⟩)
    (fun context flag => ⟨0, BoundExceedsTelescope.nil context flag⟩)
    (fun context head headLevel restLevels flag rest _headTyped _restTyped headExists restExists =>
      let ⟨headBound, headBudget⟩ := headExists
      let ⟨restBound, restBudget⟩ := restExists
      ⟨headBound + restBound,
        BoundExceedsTelescope.cons context head headLevel restLevels flag rest
          (BoundExceeds.monotoneInBound (Nat.le_add_right headBound restBound) headBudget)
          (BoundExceedsTelescope.monotoneInBound (Nat.le_add_left restBound headBound) restBudget)⟩)
    d

/-- **Every formation telescope has a budget.**  The `DescTelescope.rec` twin of `BoundExceeds.existsBound` (same
arm set, returns the telescope motive); supplies the bound that the genFormation arm of the bounded grown FT reads
off its premises telescope. -/
theorem BoundExceedsTelescope.existsBound {profile : PolyProfile} {env : Nat → Nat}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)} {levels : List LevelExpr}
    {flag : UniverseFlag} {children : RawTermChildren binderShifts baseScope}
    (t : DescTelescope profile context levels flag children) :
    ∃ bound, BoundExceedsTelescope env bound t :=
  DescTelescope.rec
    (motive_1 := fun {_scope} _context _subject _classifier d => ∃ bound, BoundExceeds env bound d)
    (motive_2 := fun {_baseScope _currentDepth _binderShifts} _context _levels _flag _children t =>
      ∃ bound, BoundExceedsTelescope env bound t)
    (fun context index => ⟨0, BoundExceeds.var context index⟩)
    (fun levelExpr flag _typed converts _reclassifierTyped subjectExists reclassifierExists =>
      let ⟨subjectBound, subjectBudget⟩ := subjectExists
      let ⟨reclassifierBound, reclassifierBudget⟩ := reclassifierExists
      ⟨subjectBound + reclassifierBound,
        BoundExceeds.conv (converts := converts) levelExpr flag
          (BoundExceeds.monotoneInBound (Nat.le_add_right subjectBound reclassifierBound) subjectBudget)
          (BoundExceeds.monotoneInBound (Nat.le_add_left reclassifierBound subjectBound) reclassifierBudget)⟩)
    (fun context levelExpr flag =>
      ⟨LevelExpr.denote (LevelExpr.lsucc levelExpr) env + 1,
        BoundExceeds.universeFormation context levelExpr flag (Nat.lt_succ_self _)⟩)
    (fun context generator payload children levels flag rule isFormation _premises premisesExists =>
      let ⟨premisesBound, premisesBudget⟩ := premisesExists
      ⟨premisesBound,
        BoundExceeds.genFormation context generator payload children levels flag rule isFormation
          premisesBudget⟩)
    (fun context flag => ⟨0, BoundExceedsTelescope.nil context flag⟩)
    (fun context head headLevel restLevels flag rest _headTyped _restTyped headExists restExists =>
      let ⟨headBound, headBudget⟩ := headExists
      let ⟨restBound, restBudget⟩ := restExists
      ⟨headBound + restBound,
        BoundExceedsTelescope.cons context head headLevel restLevels flag rest
          (BoundExceeds.monotoneInBound (Nat.le_add_right headBound restBound) headBudget)
          (BoundExceedsTelescope.monotoneInBound (Nat.le_add_left restBound headBound) restBudget)⟩)
    t

end FX1Poly.Typed
