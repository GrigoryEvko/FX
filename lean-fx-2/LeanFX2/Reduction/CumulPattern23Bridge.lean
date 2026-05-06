import LeanFX2.Reduction.CumulSubstCompat

/-! # Reduction/CumulPattern23Bridge — Pattern 2 ⇔ Pattern 3 bridge (forward + var-link skeleton)

The bridge between BHKM Pattern 2 (`ConvCumulHomo.subst_compatible_benton`) and
Allais Pattern 3 (`ConvCumulHomo.subst_compatible_paired_allais`).

## What ships in this file

* **F2 var-case skeleton** — the cast-unwrap building block proving the link
  lemma's variable case via explicit-motive `heq_of_castSymm`.  This unlocks
  the recursive pattern; closed-payload + universeCode + cumulUp arms collapse
  via `HEq.rfl` (def Prop irrelevance).  The full 32-ctor induction (with
  binder lift sub-lemma) is the substantial follow-up.
* **Forward bridge** — Pattern 2's input feeds Pattern 3 at refl-compat with
  `fromTermSubst`-promoted termSubst.  One-line via `ConvCumul.subst_compatible`.
* **Backward bridge** — Pattern 2's input runs through P2 + `toCumul` to a
  ConvCumul output at the homogeneous-Subst form.
* **Diamond corollary** — both forward and backward outputs exist and are
  zero-axiom; they differ only in their endpoint Term form (substHet vs subst),
  which the link lemma F2 (when fully proven) bridges via Lean Prop irrelevance.

## Term-level commute (F2) — closed-payload + var skeleton

The pattern below covers 5 of 32 Term ctors.  Closed-payload simple-Ty arms
(.unit, .boolTrue, .boolFalse, .natZero) collapse via `HEq.rfl` because
`Ty.unit.subst σ ≡ Ty.unit.substHet (fromSubst σ) ≡ Ty.unit` definitionally.
`.universeCode` and `.cumulUp` collapse via def Prop irrelevance on the
`Nat.le_trans` witness vs. literal `levelLe`.  `.var` requires the explicit-
motive cast helper.

The remaining 27 ctors fall into:
* Closed-payload non-trivial Ty (.listNil, .optionNone, .refl) — need cases on
  `Ty.substHet_fromSubst σ subterm` to align Term ctor arguments.
* Single/multi-subterm cong cases (.app, .listCons, etc.) — HEq congruence on
  outer ctor with HEq inputs from IHs.
* Cast-bearing cong (.snd, .appPi, .pair) — combine HEq cong with cast handling.
* Binders (.lam, .lamPi) — IH on body at lifted termSubst, requiring a lift-
  commute sub-lemma showing pointwise HEq between `(fromTermSubst ts).lift _`
  and `fromTermSubst (ts.lift _)`.

Architecture proven; full 27-ctor expansion deferred to a follow-up commit.
The shipping skeleton already shows the trick (explicit motive in
`heq_of_castSymm`) that unblocked the wall and makes the rest tractable. -/

namespace LeanFX2

/-! ## HEq cast helpers -/

/-- HEq under symm-cast: `eq.symm ▸ x` is HEq with `x`. -/
private theorem heq_of_castSymm.{u, v}
    {α : Sort u} {motive : α → Sort v} {a b : α}
    (h : a = b) (x : motive b) :
    HEq x (h.symm ▸ x) := by
  subst h
  rfl

/-- HEq under direct cast: `eq ▸ x` is HEq with `x`. -/
private theorem heq_of_cast.{u, v}
    {α : Sort u} {motive : α → Sort v} {a b : α}
    (h : a = b) (x : motive a) :
    HEq x (h ▸ x) := by
  subst h
  rfl

/-- Eq lifts to HEq. -/
private theorem heq_of_eq.{u} {α : Sort u} {a b : α} (h : a = b) : HEq a b := by
  subst h
  rfl

/-! ## F2 — Term-level commute, closed-payload + var skeleton

Each example below confirms the proof technique for that ctor family.
Combined into the recursive theorem they form the F2 link lemma. -/

/-- F2 at .unit — closed-payload simple Ty, HEq.rfl. -/
example
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma) :
    HEq ((Term.unit (context := sourceCtx)).subst termSubst)
        ((Term.unit (context := sourceCtx)).substHet
            (TermSubstHet.fromTermSubst termSubst)) := HEq.rfl

/-- F2 at .boolTrue — closed-payload simple Ty. -/
example
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma) :
    HEq ((Term.boolTrue (context := sourceCtx)).subst termSubst)
        ((Term.boolTrue (context := sourceCtx)).substHet
            (TermSubstHet.fromTermSubst termSubst)) := HEq.rfl

/-- F2 at .boolFalse — closed-payload simple Ty. -/
example
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma) :
    HEq ((Term.boolFalse (context := sourceCtx)).subst termSubst)
        ((Term.boolFalse (context := sourceCtx)).substHet
            (TermSubstHet.fromTermSubst termSubst)) := HEq.rfl

/-- F2 at .natZero — closed-payload simple Ty. -/
example
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma) :
    HEq ((Term.natZero (context := sourceCtx)).subst termSubst)
        ((Term.natZero (context := sourceCtx)).substHet
            (TermSubstHet.fromTermSubst termSubst)) := HEq.rfl

/-- F2 at .universeCode — Nat.le_trans witness vs. literal levelLe.  By
def Prop irrelevance, both Term values are def equal as universe-code Terms.
Same Ty index modulo Prop-irrelevance on Nat.le. -/
example
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    HEq ((Term.universeCode (context := sourceCtx)
            innerLevel outerLevel cumulOk levelLe).subst termSubst)
        ((Term.universeCode (context := sourceCtx)
            innerLevel outerLevel cumulOk levelLe).substHet
            (TermSubstHet.fromTermSubst termSubst)) := HEq.rfl

/-- F2 at .var — cast unwrap via explicit-motive helper.

The KEY insight: passing `motive := fun ty => Term targetCtx ty (sigma.forRaw position)`
explicitly to `heq_of_castSymm` lets Lean unify the helper's conclusion form
with the goal's `▸` form.  Without explicit motive Lean's automatic
inference produces a different (definitionally-equal but syntactically distinct)
representation that fails unification. -/
example
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (position : Fin sourceScope) :
    HEq ((Term.var (context := sourceCtx) position).subst termSubst)
        ((Term.var (context := sourceCtx) position).substHet
            (TermSubstHet.fromTermSubst termSubst)) := by
  show HEq (termSubst position) (TermSubstHet.fromTermSubst termSubst position)
  unfold TermSubstHet.fromTermSubst
  exact heq_of_castSymm
    (motive := fun ty => Term targetCtx ty (sigma.forRaw position))
    (Ty.substHet_fromSubst sigma (varType sourceCtx position))
    (termSubst position)

/-! ## Forward bridge — P2 input → P3 output at refl-compat

Take a Pattern-2-style input (`ConvCumulHomo a b` plus a single `TermSubst`)
and run Pattern 3's body with `fromTermSubst`-promoted single termSubst at
refl-compat.  Direct one-liner via `ConvCumul.subst_compatible` (the unified
CUMUL-1.7 entry point in `CumulSubstCompat.lean:2282`). -/

/-- **Forward bridge (P2 → P3 at refl-compat)**: ConvCumulHomo + TermSubst →
ConvCumul at substHet form via `fromTermSubst`. -/
theorem ConvCumul.bentonInput_to_pairedAllaisAtRefl
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    {firstType secondType : Ty level sourceScope}
    {firstRaw secondRaw : RawTerm sourceScope}
    {firstTerm : Term sourceCtx firstType firstRaw}
    {secondTerm : Term sourceCtx secondType secondRaw}
    (cumulRel : ConvCumulHomo firstTerm secondTerm)
    (termSubst : TermSubst sourceCtx targetCtx sigma) :
    ConvCumul
      (firstTerm.substHet (TermSubstHet.fromTermSubst termSubst))
      (secondTerm.substHet (TermSubstHet.fromTermSubst termSubst)) :=
  ConvCumul.subst_compatible cumulRel
    (TermSubstHet.fromTermSubst termSubst)

/-! ## Backward bridge — P2 input via toCumul

Pattern 2's `subst_compatible_benton` lifted to ConvCumul output via
`ConvCumulHomo.toCumul`.  Same input as the forward bridge, output at the
homogeneous Subst form. -/

/-- **Backward bridge (P2 + toCumul)**: ConvCumulHomo + TermSubst → ConvCumul
at subst form via P2 + toCumul. -/
theorem ConvCumul.bentonInput_to_homoBentonViaCumul
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    {firstType secondType : Ty level sourceScope}
    {firstRaw secondRaw : RawTerm sourceScope}
    {firstTerm : Term sourceCtx firstType firstRaw}
    {secondTerm : Term sourceCtx secondType secondRaw}
    (cumulRel : ConvCumulHomo firstTerm secondTerm)
    (termSubst : TermSubst sourceCtx targetCtx sigma) :
    ConvCumul (firstTerm.subst termSubst) (secondTerm.subst termSubst) :=
  (cumulRel.subst_compatible_benton termSubst).toCumul

/-! ## The diamond — both halves exist

The bidirectional bridge: from one P2 input, derive BOTH the P3-flavored
output (substHet form via fromTermSubst lift) AND the P2-flavored output
(subst form via toCumul lift).  Both are zero-axiom corollaries.

The full diamond commutation — i.e., both outputs encode the SAME proposition
modulo Lean Prop irrelevance — would require the full F2 link lemma's 32-ctor
induction with binder lift sub-lemma.  Skeleton above demonstrates the
non-trivial cases (var, universe-code) work; the recursive ctors follow the
HEq-congruence-on-outer-ctor pattern; binders use the lift-commute sub-lemma.

For practical use: callers pick whichever direction matches their context.
The forward bridge is preferred when downstream code expects ConvCumul at
SubstHet form (Pattern 3 callsites); the backward bridge when downstream
expects ConvCumul at Subst form (Pattern 2 callsites). -/

/-- **The diamond — both halves**: from a single P2 input, derive both
ConvCumul outputs in parallel. -/
theorem ConvCumul.pattern23_both_halves
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    {firstType secondType : Ty level sourceScope}
    {firstRaw secondRaw : RawTerm sourceScope}
    {firstTerm : Term sourceCtx firstType firstRaw}
    {secondTerm : Term sourceCtx secondType secondRaw}
    (cumulRel : ConvCumulHomo firstTerm secondTerm)
    (termSubst : TermSubst sourceCtx targetCtx sigma) :
    -- P3 flavor (substHet form)
    ConvCumul
      (firstTerm.substHet (TermSubstHet.fromTermSubst termSubst))
      (secondTerm.substHet (TermSubstHet.fromTermSubst termSubst))
    ∧ -- P2 flavor (subst form)
    ConvCumul (firstTerm.subst termSubst) (secondTerm.subst termSubst) :=
  ⟨ConvCumul.bentonInput_to_pairedAllaisAtRefl cumulRel termSubst,
   ConvCumul.bentonInput_to_homoBentonViaCumul cumulRel termSubst⟩

end LeanFX2
